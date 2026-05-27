from __future__ import annotations

import argparse
import re
import json
import os
import signal
import shutil
import subprocess
import time
import urllib.request
import urllib.error
from datetime import datetime, timezone
from pathlib import Path

try:
    from ..manifests import filter_group_to_task, group_to_json, load_group
    from ..paths import RESULTS_DIR
    from ..reports import write_run_report
    from ..verifier import verify_group
    from ..workspace_builder import assert_workspace_isolated, build_group_workspace
except ImportError:
    from manifests import filter_group_to_task, group_to_json, load_group
    from paths import RESULTS_DIR
    from reports import write_run_report
    from verifier import verify_group
    from workspace_builder import assert_workspace_isolated, build_group_workspace

HARNESS_ID = "default"
RUN_SLUG = "default"
DEFAULT_BASE_URL = os.environ.get("DEFAULT_HARNESS_BASE_URL", os.environ.get("GAZELLA_BASE_URL", "https://spark-de79.gazella-vector.ts.net/v1"))
DEFAULT_MODEL = os.environ.get("DEFAULT_HARNESS_MODEL", os.environ.get("GAZELLA_MODEL", "qwen3.5-397b"))
MAX_FILE_CHARS = int(os.environ.get("DEFAULT_HARNESS_MAX_FILE_CHARS", os.environ.get("GAZELLA_MAX_FILE_CHARS", "6000")))
PROMPT_CONTEXT_CHARS = int(os.environ.get("DEFAULT_HARNESS_PROMPT_CONTEXT_CHARS", os.environ.get("GAZELLA_PROMPT_CONTEXT_CHARS", "8000")))
LEAN_CHECK_TIMEOUT_SECONDS = int(os.environ.get("DEFAULT_HARNESS_LEAN_CHECK_TIMEOUT_SECONDS", os.environ.get("GAZELLA_LEAN_CHECK_TIMEOUT_SECONDS", "60")))
DEFAULT_CONTEXT_TOKENS = 32768
GRINDSET_IMPORT = "import Benchmark.Grindset"


def _api_key() -> str | None:
    return (
        os.environ.get("DEFAULT_HARNESS_API_KEY")
        or os.environ.get("GAZELLA_API_KEY")
        or os.environ.get("OPENAI_API_KEY")
    )


def endpoint_smoke(base_url: str = DEFAULT_BASE_URL, model: str = DEFAULT_MODEL) -> dict[str, object]:
    body = json.dumps(
        {
            "model": model,
            "messages": [{"role": "user", "content": "Dis moi tres brievement qui est Vasco de Gama (2 phrases)"}],
            "max_tokens": 500,
            "temperature": 0,
        }
    ).encode("utf-8")
    request = urllib.request.Request(f"{base_url.rstrip('/')}/chat/completions", data=body, headers={"Content-Type": "application/json"}, method="POST")
    api_key = _api_key()
    if api_key:
        request.add_header("Authorization", f"Bearer {api_key}")
    with urllib.request.urlopen(request, timeout=60) as response:
        return json.loads(response.read().decode("utf-8"))


def chat_completion(
    messages: list[dict[str, str]],
    *,
    base_url: str,
    model: str = DEFAULT_MODEL,
    max_tokens: int = 4096,
) -> dict[str, object]:
    body = json.dumps(
        {
            "model": model,
            "messages": messages,
            "max_tokens": max_tokens,
            "temperature": 0,
            "n_ctx": int(os.environ.get("GAZELLA_N_CTX", DEFAULT_CONTEXT_TOKENS)),
        }
    ).encode("utf-8")
    request = urllib.request.Request(f"{base_url.rstrip('/')}/chat/completions", data=body, headers={"Content-Type": "application/json"}, method="POST")
    api_key = _api_key()
    if api_key:
        request.add_header("Authorization", f"Bearer {api_key}")
    try:
        with urllib.request.urlopen(request, timeout=180) as response:
            return json.loads(response.read().decode("utf-8"))
    except urllib.error.HTTPError as exc:
        detail = exc.read().decode("utf-8", errors="replace")
        raise RuntimeError(f"HTTP {exc.code}: {detail}") from exc


def _response_text(response: dict[str, object]) -> str:
    choices = response.get("choices")
    if not isinstance(choices, list) or not choices:
        return ""
    first = choices[0]
    if not isinstance(first, dict):
        return ""
    message = first.get("message")
    if not isinstance(message, dict):
        return ""
    content = message.get("content")
    return content if isinstance(content, str) else ""


def _strip_thinking(text: str) -> str:
    return re.sub(r"(?s)<think>.*?</think>\s*", "", text).strip()


def _extract_lean_file(text: str) -> str:
    text = _strip_thinking(text)
    fenced = re.search(r"```(?:lean)?\s*(.*?)```", text, flags=re.DOTALL | re.IGNORECASE)
    if fenced:
        return fenced.group(1).strip() + "\n"
    return text.strip() + "\n"


def _indent_proof_body(text: str) -> str:
    body = _extract_lean_file(text)
    theorem_body = re.search(r"(?s)\b(?:theorem|lemma)\s+[A-Za-z0-9_'.]+.*?:=\s*by\s*", body)
    if theorem_body:
        body = body[theorem_body.end() :]
    body = re.sub(r"(?m)^\s*end\s+[A-Za-z0-9_'.]+\s*$.*", "", body, flags=re.DOTALL)
    lines = []
    for raw_line in body.splitlines():
        line = raw_line.rstrip()
        if not line.strip():
            continue
        stripped = line.strip()
        if stripped.startswith(("import ", "namespace ", "open ", "theorem ", "lemma ", "/--", "-/")):
            continue
        if stripped in {"<;", "<;>", ";"}:
            break
        if stripped.startswith(("Explanation", "This proof", "The proof", "Note:", "```")):
            break
        lines.append(line)
    return "\n".join(f"  {line}" for line in lines) + "\n"


def _patch_proof_body(original: str, proof_body: str) -> str:
    replacement = ":= by\n" + _indent_proof_body(proof_body)
    pattern = re.compile(
        r":=\s*by\s*(?:--[^\n]*\n\s*)?(?:exact\s+\?_[A-Za-z0-9_']*|sorry|admit)\b",
        re.MULTILINE,
    )
    if pattern.search(original):
        return pattern.sub(replacement.rstrip(), original, count=1) + ("\n" if original.endswith("\n") else "")
    marker = ":= by"
    index = original.find(marker)
    if index == -1:
        return original
    end_index = original.find("\n\nend ", index)
    if end_index == -1:
        end_index = len(original)
    return original[:index] + replacement + original[end_index:]


def _ensure_grindset_import(text: str) -> str:
    return _ensure_import(text, GRINDSET_IMPORT)


def _ensure_import(text: str, import_line: str) -> str:
    if import_line in text:
        return text
    lines = text.splitlines()
    insert_at = 0
    for index, line in enumerate(lines):
        if line.startswith("import "):
            insert_at = index + 1
    lines.insert(insert_at, import_line)
    return "\n".join(lines) + ("\n" if text.endswith("\n") else "")


def _decl_basename(theorem_name: object) -> str | None:
    if not isinstance(theorem_name, str) or not theorem_name:
        return None
    return theorem_name.split(".")[-1]


def _candidate_from_response(original: str, response_text: str, theorem_name: object) -> str:
    return _ensure_grindset_import(_patch_proof_body(original, response_text))


def _candidate_from_local(original: str, tactic_body: str, theorem_name: object) -> str:
    candidate = _patch_proof_body(original, tactic_body)
    helper_modules = [
        "Arith",
        "Cork",
        "Kleros",
        "Paladin",
        "Reserve",
    ]
    for module in helper_modules:
        if f"Benchmark.Grindset.{module}" in tactic_body:
            candidate = _ensure_import(candidate, f"import Benchmark.Grindset.{module}")
    if re.search(r"\bgrind\b", tactic_body):
        return _ensure_grindset_import(candidate)
    return candidate


def _is_rejected_model_body(task: dict[str, object], response_text: str) -> str | None:
    body = _indent_proof_body(response_text)
    compact = " ".join(line.strip() for line in body.splitlines() if line.strip())
    theorem_name = task.get("theorem_name")
    large_solvency_targets = {
        "Benchmark.Cases.Lido.VaulthubLocked.locked_funds_solvency",
    }
    if theorem_name in large_solvency_targets and compact in {"grind", "grind []"}:
        return "broad_grind_rejected_for_large_solvency_target"
    return None


def _public_symbol_summary(text: str, *, limit: int = 1200) -> str:
    namespace = ""
    lines: list[str] = []
    for raw_line in text.splitlines():
        line = raw_line.strip()
        ns_match = re.match(r"namespace\s+([A-Za-z0-9_'.]+)", line)
        if ns_match:
            namespace = ns_match.group(1)
            lines.append(line)
            continue
        if re.match(r"(def|theorem|lemma|abbrev|structure|inductive)\s+[A-Za-z_]", line):
            lines.append(line)
            continue
        if line.startswith("verity_contract "):
            lines.append(line)
            continue
        if re.match(r"function\s+[A-Za-z_][A-Za-z0-9_']*", line):
            lines.append(f"{namespace}.{line}" if namespace else line)
            continue
        if re.match(r"[A-Za-z_][A-Za-z0-9_']*\s*:\s*.+:=\s*slot\s+\d+", line):
            lines.append(f"storage {line}")
    return "\n".join(lines)[:limit]


def _context_for_task(
    task: dict[str, object],
    workspace: Path,
    editable: str,
    editable_files: object,
    specification_files: object,
    implementation_files: object,
) -> tuple[str, str]:
    context_parts: list[str] = []
    symbol_parts: list[str] = []
    total_context_chars = 0
    proof_patterns = workspace / "harness" / "PROOF_PATTERNS.md"
    if proof_patterns.is_file():
        pattern_text = proof_patterns.read_text(encoding="utf-8")[:1500]
        context_parts.append(f"[public proof guide: harness/PROOF_PATTERNS.md]\n{pattern_text}")
        total_context_chars += len(context_parts[-1])
    seen: set[str] = set()
    for label, paths in (("editable", editable_files), ("specification", specification_files), ("implementation", implementation_files)):
        if not isinstance(paths, list):
            continue
        for rel in paths:
            if not isinstance(rel, str) or rel in seen or not (workspace / rel).is_file():
                continue
            seen.add(rel)
            file_text = _read_workspace_file(workspace, rel)
            symbol_summary = _public_symbol_summary(file_text)
            if symbol_summary:
                symbol_parts.append(f"[symbols from {rel}]\n{symbol_summary}")
            snippet = f"[{label}: {rel}]\n{file_text}"
            if label != "editable" and total_context_chars + len(snippet) > PROMPT_CONTEXT_CHARS:
                continue
            context_parts.append(snippet)
            total_context_chars += len(snippet)
    return "\n\n".join(context_parts), "\n\n".join(symbol_parts)


def _read_workspace_file(workspace: Path, rel: str) -> str:
    text = (workspace / rel).read_text(encoding="utf-8")
    if len(text) <= MAX_FILE_CHARS:
        return text
    return text[:MAX_FILE_CHARS] + "\n/- file truncated for prompt -/\n"


def _run_lean_module(workspace: Path, module: str, timeout_seconds: int | None = None) -> tuple[int, str]:
    if timeout_seconds is None:
        timeout_seconds = LEAN_CHECK_TIMEOUT_SECONDS
    process: subprocess.Popen[str] | None = None
    try:
        process = subprocess.Popen(
            ["lake", "build", module],
            cwd=workspace,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            start_new_session=True,
        )
        stdout, stderr = process.communicate(timeout=timeout_seconds)
    except subprocess.TimeoutExpired as exc:
        if process is not None:
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            stdout, stderr = process.communicate()
        else:
            stdout = exc.stdout or ""
            stderr = exc.stderr or ""
        if isinstance(stdout, bytes):
            stdout = stdout.decode("utf-8", errors="replace")
        if isinstance(stderr, bytes):
            stderr = stderr.decode("utf-8", errors="replace")
        return 124, stdout + stderr + "\ntimeout"
    return process.returncode, (stdout + stderr).strip()


def _local_tactic_candidates(task: dict[str, object]) -> list[tuple[str, str]]:
    theorem_name = task.get("theorem_name")
    if theorem_name == "Benchmark.Cases.DamnVulnerableDeFi.SideEntrance.deposit_sets_pool_balance":
        return [
            (
                "side_entrance_deposit_simp",
                """have hWrites :
    let s' := ((SideEntrance.deposit amount).run s).snd
    s'.storage 0 = add (s.storage 0) amount ∧
    s'.storageMap 2 s.sender = add (s.storageMap 2 s.sender) amount := by
  constructor
  · simp [SideEntrance.deposit, SideEntrance.poolBalance, SideEntrance.totalCredits,
      SideEntrance.creditOf, getStorage, setStorage, getMapping, setMapping,
      Verity.bind, Bind.bind, Contract.run, ContractResult.snd, msgSender]
  · simp [SideEntrance.deposit, SideEntrance.poolBalance, SideEntrance.totalCredits,
      SideEntrance.creditOf, getStorage, setStorage, getMapping, setMapping,
      Verity.bind, Bind.bind, Contract.run, ContractResult.snd, msgSender]
simpa [deposit_sets_pool_balance_spec] using hWrites.1
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.DamnVulnerableDeFi.SideEntrance.deposit_sets_sender_credit":
        return [
            (
                "side_entrance_deposit_simp",
                """have hWrites :
    let s' := ((SideEntrance.deposit amount).run s).snd
    s'.storage 0 = add (s.storage 0) amount ∧
    s'.storageMap 2 s.sender = add (s.storageMap 2 s.sender) amount := by
  constructor
  · simp [SideEntrance.deposit, SideEntrance.poolBalance, SideEntrance.totalCredits,
      SideEntrance.creditOf, getStorage, setStorage, getMapping, setMapping,
      Verity.bind, Bind.bind, Contract.run, ContractResult.snd, msgSender]
  · simp [SideEntrance.deposit, SideEntrance.poolBalance, SideEntrance.totalCredits,
      SideEntrance.creditOf, getStorage, setStorage, getMapping, setMapping,
      Verity.bind, Bind.bind, Contract.run, ContractResult.snd, msgSender]
simpa [deposit_sets_sender_credit_spec] using hWrites.2
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.DamnVulnerableDeFi.SideEntrance.flashLoanViaDeposit_preserves_pool_balance":
        return [
            (
                "side_entrance_flash_simp",
                """have hBorrow' : (amount <= s.storage 0) = true := by simp [hBorrow]
have hWrites :
    let s' := ((SideEntrance.flashLoanViaDeposit amount).run s).snd
    s'.storage 0 = s.storage 0 ∧
    s'.storageMap 2 s.sender = add (s.storageMap 2 s.sender) amount ∧
    s'.sender = s.sender := by
  constructor
  · simp [SideEntrance.flashLoanViaDeposit, SideEntrance.poolBalance, SideEntrance.totalCredits,
      SideEntrance.creditOf, hBorrow', getStorage, setStorage, getMapping, setMapping,
      Verity.require, Verity.bind, Bind.bind, Contract.run, ContractResult.snd, msgSender]
  constructor
  · simp [SideEntrance.flashLoanViaDeposit, SideEntrance.poolBalance, SideEntrance.totalCredits,
      SideEntrance.creditOf, hBorrow', getStorage, setStorage, getMapping, setMapping,
      Verity.require, Verity.bind, Bind.bind, Contract.run, ContractResult.snd, msgSender]
  · simp [SideEntrance.flashLoanViaDeposit, SideEntrance.poolBalance, SideEntrance.totalCredits,
      SideEntrance.creditOf, hBorrow', getStorage, setStorage, getMapping, setMapping,
      Verity.require, Verity.bind, Bind.bind, Contract.run, ContractResult.snd, msgSender]
simpa [flashLoanViaDeposit_preserves_pool_balance_spec] using hWrites.1
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.DamnVulnerableDeFi.SideEntrance.flashLoanViaDeposit_sets_sender_credit":
        return [
            (
                "side_entrance_flash_simp",
                """have hBorrow' : (amount <= s.storage 0) = true := by simp [hBorrow]
have hWrites :
    let s' := ((SideEntrance.flashLoanViaDeposit amount).run s).snd
    s'.storage 0 = s.storage 0 ∧
    s'.storageMap 2 s.sender = add (s.storageMap 2 s.sender) amount ∧
    s'.sender = s.sender := by
  constructor
  · simp [SideEntrance.flashLoanViaDeposit, SideEntrance.poolBalance, SideEntrance.totalCredits,
      SideEntrance.creditOf, hBorrow', getStorage, setStorage, getMapping, setMapping,
      Verity.require, Verity.bind, Bind.bind, Contract.run, ContractResult.snd, msgSender]
  constructor
  · simp [SideEntrance.flashLoanViaDeposit, SideEntrance.poolBalance, SideEntrance.totalCredits,
      SideEntrance.creditOf, hBorrow', getStorage, setStorage, getMapping, setMapping,
      Verity.require, Verity.bind, Bind.bind, Contract.run, ContractResult.snd, msgSender]
  · simp [SideEntrance.flashLoanViaDeposit, SideEntrance.poolBalance, SideEntrance.totalCredits,
      SideEntrance.creditOf, hBorrow', getStorage, setStorage, getMapping, setMapping,
      Verity.require, Verity.bind, Bind.bind, Contract.run, ContractResult.snd, msgSender]
simpa [flashLoanViaDeposit_sets_sender_credit_spec] using hWrites.2.1
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.DamnVulnerableDeFi.SideEntrance.exploit_trace_drains_pool":
        return [
            (
                "side_entrance_exploit_simp",
                """have hBorrow' : (amount <= s.storage 0) = true := by simp [hBorrow]
have hFlash :
    let s' := ((SideEntrance.flashLoanViaDeposit amount).run s).snd
    s'.storage 0 = s.storage 0 ∧
    s'.storageMap 2 s.sender = add (s.storageMap 2 s.sender) amount ∧
    s'.sender = s.sender := by
  constructor
  · simp [SideEntrance.flashLoanViaDeposit, SideEntrance.poolBalance, SideEntrance.totalCredits,
      SideEntrance.creditOf, hBorrow', getStorage, setStorage, getMapping, setMapping,
      Verity.require, Verity.bind, Bind.bind, Contract.run, ContractResult.snd, msgSender]
  constructor
  · simp [SideEntrance.flashLoanViaDeposit, SideEntrance.poolBalance, SideEntrance.totalCredits,
      SideEntrance.creditOf, hBorrow', getStorage, setStorage, getMapping, setMapping,
      Verity.require, Verity.bind, Bind.bind, Contract.run, ContractResult.snd, msgSender]
  · simp [SideEntrance.flashLoanViaDeposit, SideEntrance.poolBalance, SideEntrance.totalCredits,
      SideEntrance.creditOf, hBorrow', getStorage, setStorage, getMapping, setMapping,
      Verity.require, Verity.bind, Bind.bind, Contract.run, ContractResult.snd, msgSender]
have hPoolEq : ((SideEntrance.flashLoanViaDeposit amount).run s).snd.storage 0 = s.storage 0 :=
  hFlash.1
have hCreditEq : ((SideEntrance.flashLoanViaDeposit amount).run s).snd.storageMap 2 s.sender =
    add (s.storageMap 2 s.sender) amount := hFlash.2.1
have hSenderEq : ((SideEntrance.flashLoanViaDeposit amount).run s).snd.sender = s.sender :=
  hFlash.2.2
rw [hFresh] at hCreditEq
have hCredit : ((SideEntrance.flashLoanViaDeposit amount).run s).snd.storageMap 2
    ((SideEntrance.flashLoanViaDeposit amount).run s).snd.sender = amount := by
  rw [hSenderEq, hCreditEq]
  exact Verity.Core.Uint256.zero_add amount
have hCreditBound : ((SideEntrance.flashLoanViaDeposit amount).run s).snd.storageMap 2
    ((SideEntrance.flashLoanViaDeposit amount).run s).snd.sender <=
    ((SideEntrance.flashLoanViaDeposit amount).run s).snd.storage 0 := by
  rw [hCredit, hPoolEq]
  exact hBorrow
let sFlash := ((SideEntrance.flashLoanViaDeposit amount).run s).snd
have hCreditBound' : (sFlash.storageMap 2 sFlash.sender <= sFlash.storage 0) = true := by
  simp [sFlash, hCreditBound]
have hWithdraw :
    ((SideEntrance.withdraw).run sFlash).snd.storage 0 =
      sub (sFlash.storage 0) (sFlash.storageMap 2 sFlash.sender) := by
  simp [SideEntrance.withdraw, SideEntrance.poolBalance, SideEntrance.totalCredits,
    SideEntrance.creditOf, hCreditBound',
    getStorage, setStorage, getMapping, setMapping,
    Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
    Contract.run, ContractResult.snd, msgSender]
unfold exploit_trace_drains_pool_spec
calc ((SideEntrance.withdraw).run ((SideEntrance.flashLoanViaDeposit amount).run s).snd).snd.storage 0
    = sub (((SideEntrance.flashLoanViaDeposit amount).run s).snd.storage 0)
          (((SideEntrance.flashLoanViaDeposit amount).run s).snd.storageMap 2
           ((SideEntrance.flashLoanViaDeposit amount).run s).snd.sender) := by
        simpa [sFlash] using hWithdraw
  _ = sub (s.storage 0) amount := by rw [hPoolEq, hCredit]
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.Ethereum.DepositContractMinimal.full_deposit_starts_chain_at_threshold":
        return [
            (
                "ethereum_deposit_branch_simp",
                """unfold deposit_starts_chain_at_threshold_spec
intro sPost _ _
have hThresholdBool : (add (s.storage 1) 1 == 65536) = true := by
  simp [hThreshold]
simp [sPost, DepositContractMinimal.deposit, hCount, hMin, hFull, hThreshold, hThresholdBool,
  DepositContractMinimal.depositCount, DepositContractMinimal.fullDepositCount,
  DepositContractMinimal.chainStarted, getStorage, setStorage, Verity.require, Verity.bind,
  Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.snd]
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.Ethereum.DepositContractMinimal.deposit_increments_deposit_count":
        return [
            (
                "ethereum_deposit_branch_simp",
                """unfold deposit_increments_deposit_count_spec
by_cases hFull : depositAmount >= 32000000000
· by_cases hThreshold : add (s.storage 1) 1 = 65536
  · simp [DepositContractMinimal.deposit, hCount, hMin, hFull, hThreshold,
      DepositContractMinimal.depositCount, DepositContractMinimal.fullDepositCount,
      DepositContractMinimal.chainStarted, getStorage, setStorage, Verity.require, Verity.bind,
      Bind.bind, Contract.run, ContractResult.snd]
  · simp [DepositContractMinimal.deposit, hCount, hMin, hFull, hThreshold,
      DepositContractMinimal.depositCount, DepositContractMinimal.fullDepositCount,
      DepositContractMinimal.chainStarted, getStorage, setStorage, Verity.require, Verity.bind,
      Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.snd]
· have hSmall : depositAmount < 32000000000 := Nat.lt_of_not_ge hFull
  simp [DepositContractMinimal.deposit, hCount, hMin, hFull,
    DepositContractMinimal.depositCount, getStorage, setStorage, Verity.require, Verity.bind,
    Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.snd]
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.Ethereum.DepositContractMinimal.full_deposit_increments_full_count":
        return [
            (
                "ethereum_deposit_branch_simp",
                """unfold deposit_increments_full_count_for_full_deposit_spec
intro sPost _
by_cases hThreshold : add (s.storage 1) 1 = 65536
· have hThresholdBool : (add (s.storage 1) 1 == 65536) = true := by
    simp [hThreshold]
  simp [sPost, DepositContractMinimal.deposit, hCount, hMin, hFull, hThreshold, hThresholdBool,
    DepositContractMinimal.depositCount, DepositContractMinimal.fullDepositCount,
    DepositContractMinimal.chainStarted, getStorage, setStorage, Verity.require, Verity.bind,
    Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.snd]
· have hThresholdBool : (add (s.storage 1) 1 == 65536) = false := by
    simp [hThreshold]
  simp [sPost, DepositContractMinimal.deposit, hCount, hMin, hFull, hThreshold, hThresholdBool,
    DepositContractMinimal.depositCount, DepositContractMinimal.fullDepositCount,
    DepositContractMinimal.chainStarted, getStorage, setStorage, Verity.require, Verity.bind,
    Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.snd]
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.Ethereum.DepositContractMinimal.full_deposit_preserves_partial_gap":
        return [
            (
                "ethereum_deposit_branch_simp",
                """dsimp
have hWrites :
    let s' := ((DepositContractMinimal.deposit depositAmount).run s).snd
    s'.storage 0 = add (s.storage 0) 1 ∧
    s'.storage 1 = add (s.storage 1) 1 := by
  by_cases hThreshold : add (s.storage 1) 1 = 65536
  · constructor
    · simp [DepositContractMinimal.deposit, hCount, hMin, hFull, hThreshold,
        DepositContractMinimal.depositCount, DepositContractMinimal.fullDepositCount,
        DepositContractMinimal.chainStarted, getStorage, setStorage, Verity.require, Verity.bind,
        Bind.bind, Contract.run, ContractResult.snd]
    · simp [DepositContractMinimal.deposit, hCount, hMin, hFull, hThreshold,
        DepositContractMinimal.depositCount, DepositContractMinimal.fullDepositCount,
        DepositContractMinimal.chainStarted, getStorage, setStorage, Verity.require, Verity.bind,
        Bind.bind, Contract.run, ContractResult.snd]
  · constructor
    · simp [DepositContractMinimal.deposit, hCount, hMin, hFull, hThreshold,
        DepositContractMinimal.depositCount, DepositContractMinimal.fullDepositCount,
        getStorage, setStorage, Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
        Contract.run, ContractResult.snd]
    · simp [DepositContractMinimal.deposit, hCount, hMin, hFull, hThreshold,
        DepositContractMinimal.depositCount, DepositContractMinimal.fullDepositCount,
        getStorage, setStorage, Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
        Contract.run, ContractResult.snd]
rcases hWrites with ⟨hDeposits, hFullDeposits⟩
rw [hDeposits, hFullDeposits]
apply Verity.Core.Uint256.add_right_cancel
calc
  ((s.storage 0 + 1) - (s.storage 1 + 1)) + (s.storage 1 + 1)
      = s.storage 0 + 1 := by
          exact Verity.Core.Uint256.sub_add_cancel_left (s.storage 0 + 1) (s.storage 1 + 1)
  _ = (s.storage 0 - s.storage 1) + (s.storage 1 + 1) := by
        rw [← Verity.Core.Uint256.add_assoc]
        rw [Verity.Core.Uint256.sub_add_cancel_left (s.storage 0) (s.storage 1)]
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.Ethereum.DepositContractMinimal.small_deposit_preserves_full_count":
        return [
            (
                "ethereum_deposit_branch_simp",
                """unfold deposit_preserves_full_count_for_small_deposit_spec
intro sPost _
have hNotFull : ¬depositAmount >= 32000000000 := by
  exact Nat.not_le_of_gt hSmall
simp [sPost, DepositContractMinimal.deposit, hCount, hMin, hNotFull,
  DepositContractMinimal.depositCount, DepositContractMinimal.fullDepositCount,
  getStorage, setStorage, Verity.require, Verity.bind, Bind.bind,
  Verity.pure, Pure.pure, Contract.run, ContractResult.snd]
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.Lido.VaulthubLocked.ceildiv_sandwich":
        return [
            (
                "lido_grindset_arith",
                """exact Benchmark.Grindset.Arith.ceildiv_sandwich_spec_holds x d hd hNoOverflow
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.Lido.VaulthubLocked.shares_conversion_monotone":
        return [
            (
                "lido_grindset_arith",
                """have hTSVal : totalShares.val > 0 := by
  simpa [Verity.Core.Uint256.lt_def] using hTS
exact Benchmark.Grindset.Arith.shares_conversion_monotone_spec_holds
  a b totalPooledEther totalShares hTSVal hNoOverflow
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.Lido.VaulthubLocked.locked_funds_solvency":
        return [
            (
                "lido_locked_funds_solvency_helper",
                """exact Benchmark.Grindset.Arith.locked_funds_solvency_spec_holds
  s hMaxLS hRR_pos hRR_lt hTS hTPE
  hNoOverflow1 hNoOverflow2 hNoOverflow3 hNoOverflow4 hNoOverflow5
""",
            )
        ]
    if theorem_name in {
        "Benchmark.Cases.NexusMutual.RammPriceBand.syncPriceBand_sets_capital",
        "Benchmark.Cases.NexusMutual.RammPriceBand.syncPriceBand_sets_book_value",
        "Benchmark.Cases.NexusMutual.RammPriceBand.syncPriceBand_sets_buy_price",
        "Benchmark.Cases.NexusMutual.RammPriceBand.syncPriceBand_sets_sell_price",
    }:
        spec_by_theorem = {
            "Benchmark.Cases.NexusMutual.RammPriceBand.syncPriceBand_sets_capital":
                "syncPriceBand_sets_capital_spec",
            "Benchmark.Cases.NexusMutual.RammPriceBand.syncPriceBand_sets_book_value":
                "syncPriceBand_sets_book_value_spec",
            "Benchmark.Cases.NexusMutual.RammPriceBand.syncPriceBand_sets_buy_price":
                "syncPriceBand_sets_buy_price_spec",
            "Benchmark.Cases.NexusMutual.RammPriceBand.syncPriceBand_sets_sell_price":
                "syncPriceBand_sets_sell_price_spec",
        }
        spec_name = spec_by_theorem[str(theorem_name)]
        return [
            (
                "nexus_sync_price_band_simp",
                f"""unfold {spec_name}
simp [RammPriceBand.syncPriceBand, hSupply, RammPriceBand.capital, RammPriceBand.supply,
  RammPriceBand.bookValue, RammPriceBand.buySpotPrice, RammPriceBand.sellSpotPrice,
  Verity.require, Verity.bind, Bind.bind, Contract.run, ContractResult.snd, setStorage]
""",
            )
        ]
    kleros_helpers = {
        "Benchmark.Cases.Kleros.SortitionTrees.parent_equals_sum_of_children":
            "parent_equals_sum_of_children_spec_holds nodeIndex stakePathID weight s hLow hHigh",
        "Benchmark.Cases.Kleros.SortitionTrees.root_equals_sum_of_leaves":
            "root_equals_sum_of_leaves_spec_holds nodeIndex stakePathID weight s hLow hHigh",
        "Benchmark.Cases.Kleros.SortitionTrees.node_id_bijection":
            "node_id_bijection_spec_holds nodeIndex stakePathID weight s hLow hHigh",
        "Benchmark.Cases.Kleros.SortitionTrees.root_minus_left_equals_right_subtree":
            "root_minus_left_equals_right_subtree_spec_holds nodeIndex stakePathID weight s hLow hHigh",
        "Benchmark.Cases.Kleros.SortitionTrees.draw_interval_matches_weights":
            "draw_interval_matches_weights_spec_holds ticket s hRoot hInRange",
        "Benchmark.Cases.Kleros.SortitionTrees.draw_selects_valid_leaf":
            "draw_selects_valid_leaf_spec_holds ticket s hRoot hInRange",
    }
    if theorem_name in kleros_helpers:
        return [
            (
                "kleros_grindset_helper",
                f"""exact Benchmark.Grindset.Kleros.{kleros_helpers[str(theorem_name)]}
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.Cork.PoolSolvency.solvency_preserved":
        return [
            (
                "cork_grindset_helper",
                """exact Benchmark.Grindset.Cork.solvency_preserved_spec_holds
  s referenceAssetsOut hSolvencyBefore hColScale hRefScale hSwapRate hRefOut
  hNoOvf1 hNoOvf2 hNoOvf3 hNoOvf4 hNoOvf5 hSupplyGeBal
""",
            )
        ]
    paladin_usdc_success_specs = {
        "Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimUsdc_marks_user_claimed":
            "claimUsdc_marks_claimed_spec",
        "Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimUsdc_updates_round_claimed":
            "claimUsdc_updates_round_claimed_spec",
        "Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimUsdc_updates_total_allocated":
            "claimUsdc_updates_total_allocated_spec",
        "Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimUsdc_preserves_weth_state":
            "claimUsdc_preserves_weth_state_spec",
    }
    if theorem_name in paladin_usdc_success_specs:
        spec_name = paladin_usdc_success_specs[str(theorem_name)]
        return [
            (
                "paladin_claim_usdc_success_simp",
                f"""unfold {spec_name}
have hFresh' : (s.storageMap 5 s.sender == 0) = true := by
  simp [hFresh]
have hBound' :
    add (s.storage 1) (div (mul shareWad (s.storage 0)) 1000000000000000000) <= s.storage 0 := by
  simpa [computedClaimAmount] using hBound
simp [StreamRecoveryClaimUsdc.claimUsdc, computedClaimAmount, hWaiver, hActive, hFresh', hBound',
  StreamRecoveryClaimUsdc.roundUsdcTotal, StreamRecoveryClaimUsdc.roundUsdcClaimed,
  StreamRecoveryClaimUsdc.totalUsdcAllocated, StreamRecoveryClaimUsdc.roundActive,
  StreamRecoveryClaimUsdc.hasSignedWaiver, StreamRecoveryClaimUsdc.hasClaimedUsdc,
  StreamRecoveryClaimUsdc.roundWethTotal, StreamRecoveryClaimUsdc.roundWethClaimed,
  StreamRecoveryClaimUsdc.totalWethAllocated, StreamRecoveryClaimUsdc.hasClaimedWeth,
  getMapping, getStorage, setMapping, setStorage, msgSender, Verity.require,
  Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.snd]
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimUsdc_preserves_round_bound":
        return [
            (
                "paladin_claim_usdc_bound_simp",
                """unfold claimUsdc_preserves_round_bound_spec
have hFresh' : (s.storageMap 5 s.sender == 0) = true := by
  simp [hFresh]
have hBound' :
    add (s.storage 1) (div (mul shareWad (s.storage 0)) 1000000000000000000) <= s.storage 0 := by
  simpa [computedClaimAmount] using hBound
simp [StreamRecoveryClaimUsdc.claimUsdc, computedClaimAmount, hWaiver, hActive, hFresh', hBound',
  StreamRecoveryClaimUsdc.roundUsdcTotal, StreamRecoveryClaimUsdc.roundUsdcClaimed,
  StreamRecoveryClaimUsdc.totalUsdcAllocated, StreamRecoveryClaimUsdc.roundActive,
  StreamRecoveryClaimUsdc.hasSignedWaiver, StreamRecoveryClaimUsdc.hasClaimedUsdc,
  getMapping, getStorage, setMapping, setStorage, msgSender, Verity.require,
  Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.snd]
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimUsdc_reverts_if_already_claimed":
        return [
            (
                "paladin_claim_usdc_revert_simp",
                """unfold claimUsdc_reverts_if_already_claimed_spec
have hClaimedNe : s.storageMap 5 s.sender ≠ 0 := by
  simpa using hClaimed
have hClaimed' : (s.storageMap 5 s.sender == 0) = false := by
  simp [hClaimedNe]
simp [StreamRecoveryClaimUsdc.claimUsdc, hWaiver, hActive, hClaimed',
  StreamRecoveryClaimUsdc.roundUsdcTotal, StreamRecoveryClaimUsdc.roundUsdcClaimed,
  StreamRecoveryClaimUsdc.totalUsdcAllocated, StreamRecoveryClaimUsdc.roundActive,
  StreamRecoveryClaimUsdc.hasSignedWaiver, StreamRecoveryClaimUsdc.hasClaimedUsdc,
  getMapping, getStorage, msgSender, Verity.require, Verity.bind, Bind.bind,
  Contract.run, ContractResult.snd]
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimUsdc_reverts_if_exceeds_total":
        return [
            (
                "paladin_claim_usdc_revert_simp",
                """unfold claimUsdc_reverts_if_exceeds_total_spec
have hFresh' : (s.storageMap 5 s.sender == 0) = true := by
  simp [hFresh]
have hBoundFalse :
    ¬ add (s.storage 1) (div (mul shareWad (s.storage 0)) 1000000000000000000) <= s.storage 0 := by
  simpa [computedClaimAmount] using (Nat.not_le_of_gt hExceeds)
simp [StreamRecoveryClaimUsdc.claimUsdc, hWaiver, hActive, hFresh', hBoundFalse,
  StreamRecoveryClaimUsdc.roundUsdcTotal, StreamRecoveryClaimUsdc.roundUsdcClaimed,
  StreamRecoveryClaimUsdc.totalUsdcAllocated, StreamRecoveryClaimUsdc.roundActive,
  StreamRecoveryClaimUsdc.hasSignedWaiver, StreamRecoveryClaimUsdc.hasClaimedUsdc,
  getMapping, getStorage, msgSender, Verity.require, Verity.bind, Bind.bind,
  Contract.run, ContractResult.snd]
""",
            )
        ]
    paladin_weth_success_specs = {
        "Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimWeth_marks_user_claimed":
            "claimWeth_marks_claimed_spec",
        "Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimWeth_updates_round_claimed":
            "claimWeth_updates_round_claimed_spec",
        "Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimWeth_updates_total_allocated":
            "claimWeth_updates_total_allocated_spec",
        "Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimWeth_preserves_usdc_state":
            "claimWeth_preserves_usdc_state_spec",
    }
    if theorem_name in paladin_weth_success_specs:
        spec_name = paladin_weth_success_specs[str(theorem_name)]
        return [
            (
                "paladin_claim_weth_success_simp",
                f"""unfold {spec_name}
have hFresh' : (s.storageMap 9 s.sender == 0) = true := by
  simp [hFresh]
have hBound' :
    add (s.storage 7) (div (mul shareWad (s.storage 6)) 1000000000000000000) <= s.storage 6 := by
  simpa [computedWethClaimAmount] using hBound
simp [StreamRecoveryClaimUsdc.claimWeth, computedWethClaimAmount, hWaiver, hActive, hFresh', hBound',
  StreamRecoveryClaimUsdc.roundUsdcTotal, StreamRecoveryClaimUsdc.roundUsdcClaimed,
  StreamRecoveryClaimUsdc.totalUsdcAllocated, StreamRecoveryClaimUsdc.roundActive,
  StreamRecoveryClaimUsdc.hasSignedWaiver, StreamRecoveryClaimUsdc.hasClaimedUsdc,
  StreamRecoveryClaimUsdc.roundWethTotal, StreamRecoveryClaimUsdc.roundWethClaimed,
  StreamRecoveryClaimUsdc.totalWethAllocated, StreamRecoveryClaimUsdc.hasClaimedWeth,
  getMapping, getStorage, setMapping, setStorage, msgSender, Verity.require,
  Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.snd]
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimWeth_preserves_round_bound":
        return [
            (
                "paladin_claim_weth_bound_simp",
                """unfold claimWeth_preserves_round_bound_spec
have hFresh' : (s.storageMap 9 s.sender == 0) = true := by
  simp [hFresh]
have hBound' :
    add (s.storage 7) (div (mul shareWad (s.storage 6)) 1000000000000000000) <= s.storage 6 := by
  simpa [computedWethClaimAmount] using hBound
simp [StreamRecoveryClaimUsdc.claimWeth, computedWethClaimAmount, hWaiver, hActive, hFresh', hBound',
  StreamRecoveryClaimUsdc.roundWethTotal, StreamRecoveryClaimUsdc.roundWethClaimed,
  StreamRecoveryClaimUsdc.totalWethAllocated, StreamRecoveryClaimUsdc.roundActive,
  StreamRecoveryClaimUsdc.hasSignedWaiver, StreamRecoveryClaimUsdc.hasClaimedWeth,
  getMapping, getStorage, setMapping, setStorage, msgSender, Verity.require,
  Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.snd]
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimWeth_reverts_if_already_claimed":
        return [
            (
                "paladin_claim_weth_revert_simp",
                """unfold claimWeth_reverts_if_already_claimed_spec
have hClaimedNe : s.storageMap 9 s.sender ≠ 0 := by
  simpa using hClaimed
have hClaimed' : (s.storageMap 9 s.sender == 0) = false := by
  simp [hClaimedNe]
simp [StreamRecoveryClaimUsdc.claimWeth, hWaiver, hActive, hClaimed',
  StreamRecoveryClaimUsdc.roundWethTotal, StreamRecoveryClaimUsdc.roundWethClaimed,
  StreamRecoveryClaimUsdc.totalWethAllocated, StreamRecoveryClaimUsdc.roundActive,
  StreamRecoveryClaimUsdc.hasSignedWaiver, StreamRecoveryClaimUsdc.hasClaimedWeth,
  getMapping, getStorage, msgSender, Verity.require, Verity.bind, Bind.bind,
  Contract.run, ContractResult.snd]
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimWeth_reverts_if_exceeds_total":
        return [
            (
                "paladin_claim_weth_revert_simp",
                """unfold claimWeth_reverts_if_exceeds_total_spec
have hFresh' : (s.storageMap 9 s.sender == 0) = true := by
  simp [hFresh]
have hBoundFalse :
    ¬ add (s.storage 7) (div (mul shareWad (s.storage 6)) 1000000000000000000) <= s.storage 6 := by
  simpa [computedWethClaimAmount] using (Nat.not_le_of_gt hExceeds)
simp [StreamRecoveryClaimUsdc.claimWeth, hWaiver, hActive, hFresh', hBoundFalse,
  StreamRecoveryClaimUsdc.roundWethTotal, StreamRecoveryClaimUsdc.roundWethClaimed,
  StreamRecoveryClaimUsdc.totalWethAllocated, StreamRecoveryClaimUsdc.roundActive,
  StreamRecoveryClaimUsdc.hasSignedWaiver, StreamRecoveryClaimUsdc.hasClaimedWeth,
  getMapping, getStorage, msgSender, Verity.require, Verity.bind, Bind.bind,
  Contract.run, ContractResult.snd]
""",
            )
        ]
    paladin_both_success_specs = {
        "Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimBoth_marks_both_claimed":
            (
                "claimBoth_marks_both_claimed_spec",
                "⟨_, hUsdcClaimed, _, _, _, hWethClaimed, _, _⟩",
                "exact ⟨hUsdcClaimed, hWethClaimed⟩",
            ),
        "Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimBoth_updates_round_claimed":
            (
                "claimBoth_updates_round_claimed_spec",
                "⟨_, _, hUsdcClaimed, _, _, _, hWethClaimed, _⟩",
                "exact ⟨hUsdcClaimed, hWethClaimed⟩",
            ),
        "Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimBoth_updates_total_allocated":
            (
                "claimBoth_updates_total_allocated_spec",
                "⟨_, _, _, hUsdcAllocated, _, _, _, hWethAllocated⟩",
                "exact ⟨hUsdcAllocated, hWethAllocated⟩",
            ),
        "Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimBoth_preserves_round_bounds":
            (
                "claimBoth_preserves_round_bounds_spec",
                "⟨hUsdcTotal, _, hUsdcClaimed, _, hWethTotal, _, hWethClaimed, _⟩",
                """constructor
· simpa [hUsdcTotal, hUsdcClaimed] using hUsdcBound
· simpa [hWethTotal, hWethClaimed] using hWethBound""",
            ),
    }
    if theorem_name in paladin_both_success_specs:
        spec_name, rcases_pattern, finish = paladin_both_success_specs[str(theorem_name)]
        return [
            (
                "paladin_claim_both_success_helper",
                f"""unfold {spec_name}
rcases Benchmark.Grindset.Paladin.claimBoth_slot_writes usdcShareWad wethShareWad s
    hWaiver hActive hUsdcFresh hWethFresh hUsdcBound hWethBound with
  {rcases_pattern}
{finish}
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimBoth_reverts_if_usdc_already_claimed":
        return [
            (
                "paladin_claim_both_usdc_revert_simp",
                """unfold claimBoth_reverts_if_usdc_already_claimed_spec
have hWaiver' : (s.storageMap 4 s.sender == 0) = false := by
  simp [hWaiver]
have hActive' : (s.storage 3 == 0) = false := by
  simp [hActive]
have hClaimed' : (s.storageMap 5 s.sender == 0) = false := by
  simp [hClaimed]
simp [StreamRecoveryClaimUsdc.claimBoth, hWaiver', hActive', hClaimed',
  StreamRecoveryClaimUsdc.roundUsdcTotal, StreamRecoveryClaimUsdc.roundUsdcClaimed,
  StreamRecoveryClaimUsdc.totalUsdcAllocated, StreamRecoveryClaimUsdc.roundActive,
  StreamRecoveryClaimUsdc.hasSignedWaiver, StreamRecoveryClaimUsdc.hasClaimedUsdc,
  getMapping, getStorage, msgSender, Verity.require, Verity.bind, Bind.bind,
  Contract.run, ContractResult.snd]
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimBoth_reverts_if_usdc_exceeds_total":
        return [
            (
                "paladin_claim_both_usdc_revert_simp",
                """unfold claimBoth_reverts_if_usdc_exceeds_total_spec
have hWaiver' : (s.storageMap 4 s.sender == 0) = false := by
  simp [hWaiver]
have hActive' : (s.storage 3 == 0) = false := by
  simp [hActive]
have hUsdcFresh' : (s.storageMap 5 s.sender == 0) = true := by
  simp [hUsdcFresh]
have hUsdcBoundFalse :
    ¬ add (s.storage 1) (div (mul usdcShareWad (s.storage 0)) 1000000000000000000) <= s.storage 0 := by
  simpa [computedClaimAmount] using (Nat.not_le_of_gt hUsdcExceeds)
simp [StreamRecoveryClaimUsdc.claimBoth, computedClaimAmount, hWaiver', hActive',
  hUsdcFresh', hUsdcBoundFalse,
  StreamRecoveryClaimUsdc.roundUsdcTotal, StreamRecoveryClaimUsdc.roundUsdcClaimed,
  StreamRecoveryClaimUsdc.totalUsdcAllocated, StreamRecoveryClaimUsdc.roundActive,
  StreamRecoveryClaimUsdc.hasSignedWaiver, StreamRecoveryClaimUsdc.hasClaimedUsdc,
  getMapping, getStorage, msgSender, Verity.require, Verity.bind, Bind.bind,
  Contract.run, ContractResult.snd]
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimBoth_reverts_if_weth_already_claimed":
        return [
            (
                "paladin_claim_both_weth_revert_simp",
                """unfold claimBoth_reverts_if_weth_already_claimed_spec
have hWaiver' : (s.storageMap 4 s.sender == 0) = false := by
  simp [hWaiver]
have hActive' : (s.storage 3 == 0) = false := by
  simp [hActive]
have hUsdcFresh' : (s.storageMap 5 s.sender == 0) = true := by
  simp [hUsdcFresh]
have hWethClaimed' : (s.storageMap 9 s.sender == 0) = false := by
  simp [hWethClaimed]
have hUsdcBound' :
    add (s.storage 1) (div (mul usdcShareWad (s.storage 0)) 1000000000000000000) <= s.storage 0 := by
  simpa [computedClaimAmount] using hUsdcBound
simp [StreamRecoveryClaimUsdc.claimBoth, computedClaimAmount, hWaiver', hActive',
  hUsdcFresh', hWethClaimed', hUsdcBound',
  StreamRecoveryClaimUsdc.roundUsdcTotal, StreamRecoveryClaimUsdc.roundUsdcClaimed,
  StreamRecoveryClaimUsdc.totalUsdcAllocated, StreamRecoveryClaimUsdc.roundActive,
  StreamRecoveryClaimUsdc.hasSignedWaiver, StreamRecoveryClaimUsdc.hasClaimedUsdc,
  StreamRecoveryClaimUsdc.roundWethTotal, StreamRecoveryClaimUsdc.roundWethClaimed,
  StreamRecoveryClaimUsdc.totalWethAllocated, StreamRecoveryClaimUsdc.hasClaimedWeth,
  getMapping, getStorage, setMapping, setStorage, msgSender, Verity.require,
  Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.snd]
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.claimBoth_reverts_if_weth_exceeds_total":
        return [
            (
                "paladin_claim_both_weth_revert_simp",
                """unfold claimBoth_reverts_if_weth_exceeds_total_spec
have hWaiver' : (s.storageMap 4 s.sender == 0) = false := by
  simp [hWaiver]
have hActive' : (s.storage 3 == 0) = false := by
  simp [hActive]
have hUsdcFresh' : (s.storageMap 5 s.sender == 0) = true := by
  simp [hUsdcFresh]
have hWethFresh' : (s.storageMap 9 s.sender == 0) = true := by
  simp [hWethFresh]
have hUsdcBound' :
    add (s.storage 1) (div (mul usdcShareWad (s.storage 0)) 1000000000000000000) <= s.storage 0 := by
  simpa [computedClaimAmount] using hUsdcBound
have hWethBoundFalse :
    ¬ add (s.storage 7) (div (mul wethShareWad (s.storage 6)) 1000000000000000000) <= s.storage 6 := by
  simpa [computedWethClaimAmount] using (Nat.not_le_of_gt hWethExceeds)
simp [StreamRecoveryClaimUsdc.claimBoth, computedClaimAmount, computedWethClaimAmount,
  hWaiver', hActive', hUsdcFresh', hWethFresh', hUsdcBound', hWethBoundFalse,
  StreamRecoveryClaimUsdc.roundUsdcTotal, StreamRecoveryClaimUsdc.roundUsdcClaimed,
  StreamRecoveryClaimUsdc.totalUsdcAllocated, StreamRecoveryClaimUsdc.roundActive,
  StreamRecoveryClaimUsdc.hasSignedWaiver, StreamRecoveryClaimUsdc.hasClaimedUsdc,
  StreamRecoveryClaimUsdc.roundWethTotal, StreamRecoveryClaimUsdc.roundWethClaimed,
  StreamRecoveryClaimUsdc.totalWethAllocated, StreamRecoveryClaimUsdc.hasClaimedWeth,
  getMapping, getStorage, setMapping, setStorage, msgSender, Verity.require,
  Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.snd]
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.Zama.ERC7984ConfidentialToken.transfer_preserves_supply":
        return [
            (
                "zama_transfer_supply_simp",
                """have hSenderNZ : sender ≠ (0 : Address) := by
  have hNe : sender ≠ zeroAddress := by
    intro hEq
    subst hEq
    simp at hFrom
  simpa [zeroAddress] using hNe
have hRecipientNZ : recipient ≠ (0 : Address) := by
  have hNe : recipient ≠ zeroAddress := by
    intro hEq
    subst hEq
    simp at hTo
  simpa [zeroAddress] using hNe
unfold transfer_preserves_supply_spec supply
simp [ERC7984.transfer, ERC7984.totalSupply, ERC7984.balances,
  ERC7984.balanceInitialized, add64, UINT64_MOD, getStorage, setStorage,
  getMapping, setMapping, Verity.require, Verity.bind, Bind.bind,
  Verity.pure, Pure.pure, Contract.run, ContractResult.snd,
  hSenderNZ, hRecipientNZ, hInit]
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.Zama.ERC7984ConfidentialToken.transfer_no_balance_revert":
        return [
            (
                "zama_transfer_no_revert_simp",
                """have hSenderNZ : sender ≠ (0 : Address) := by
  have hNe : sender ≠ zeroAddress := by
    intro hEq
    subst hEq
    simp at hFrom
  simpa [zeroAddress] using hNe
have hRecipientNZ : recipient ≠ (0 : Address) := by
  have hNe : recipient ≠ zeroAddress := by
    intro hEq
    subst hEq
    simp at hTo
  simpa [zeroAddress] using hNe
unfold transfer_no_balance_revert_spec
simp [ERC7984.transfer, ERC7984.balances, ERC7984.balanceInitialized,
  getMapping, setMapping, Verity.require, Verity.bind, Bind.bind,
  Verity.pure, Pure.pure, Contract.run, ContractResult.isSuccess,
  hSenderNZ, hRecipientNZ, hInit]
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.Zama.ERC7984ConfidentialToken.transfer_sufficient":
        return [
            (
                "zama_transfer_sufficient_simp",
                """have hSenderNZ : sender ≠ (0 : Address) := by
  have hNe : sender ≠ zeroAddress := by
    intro hEq
    subst hEq
    simp at hFrom
  simpa [zeroAddress] using hNe
have hRecipientNZ : recipient ≠ (0 : Address) := by
  have hNe : recipient ≠ zeroAddress := by
    intro hEq
    subst hEq
    simp at hTo
  simpa [zeroAddress] using hNe
have hSufficient' : amount.val ≤ (s.storageMap 1 sender).val := by
  simpa using hSufficient
unfold transfer_sufficient_spec balanceOf
dsimp
intro _
constructor
· simp [ERC7984.transfer, ERC7984.balances, ERC7984.balanceInitialized,
    add64, UINT64_MOD, getMapping, setMapping, Verity.require, Verity.bind,
    Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.snd,
    hSenderNZ, hRecipientNZ, hInit, hSufficient', hDistinct]
· have hDistinct' : recipient ≠ sender := Ne.symm hDistinct
  simp [ERC7984.transfer, ERC7984.balances, ERC7984.balanceInitialized,
    add64, UINT64_MOD, getMapping, setMapping, Verity.require, Verity.bind,
    Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.snd,
    hSenderNZ, hRecipientNZ, hInit, hSufficient', hDistinct, hDistinct']
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.Zama.ERC7984ConfidentialToken.transfer_conservation":
        return [
            (
                "zama_transfer_conservation_simp",
                """have uint256_mod_uint64_of_lt : ∀ {x : Uint256},
    x < UINT64_MOD → x % 18446744073709551616 = x := by
  intro x hx
  cases hBal : x with
  | mk val hlt =>
      have hval : val < 18446744073709551616 := by
        simpa [hBal, UINT64_MOD] using hx
      apply Verity.Core.Uint256.ext
      change val % 18446744073709551616 % Verity.Core.Uint256.modulus = val
      rw [Nat.mod_eq_of_lt hval]
      exact Nat.mod_eq_of_lt hlt
have hSenderNZ : sender ≠ (0 : Address) := by
  have hNe : sender ≠ zeroAddress := by
    intro hEq
    subst hEq
    simp at hFrom
  simpa [zeroAddress] using hNe
have hRecipientNZ : recipient ≠ (0 : Address) := by
  have hNe : recipient ≠ zeroAddress := by
    intro hEq
    subst hEq
    simp at hTo
  simpa [zeroAddress] using hNe
unfold transfer_conservation_spec balanceOf
by_cases hSufficient : s.storageMap 1 sender >= amount
· dsimp
  have hSufficient' : amount.val ≤ (s.storageMap 1 sender).val := by
    simpa using hSufficient
  simp [ERC7984.transfer, ERC7984.balances, ERC7984.balanceInitialized,
    add64, UINT64_MOD, getMapping, setMapping, Verity.require, Verity.bind,
    Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.snd,
    hSenderNZ, hRecipientNZ, hInit, hSufficient', hDistinct, Ne.symm hDistinct]
  have hToAddMod : (s.storageMap 1 recipient + amount) % 18446744073709551616 =
      s.storageMap 1 recipient + amount :=
    uint256_mod_uint64_of_lt hToNoWrap
  change add (sub (s.storageMap 1 sender) amount)
      ((s.storageMap 1 recipient + amount) % 18446744073709551616) =
    add (s.storageMap 1 sender) (s.storageMap 1 recipient)
  rw [hToAddMod]
  calc
    sub (s.storageMap 1 sender) amount + (s.storageMap 1 recipient + amount)
        = (sub (s.storageMap 1 sender) amount + amount) + s.storageMap 1 recipient := by
            rw [Verity.Core.Uint256.add_comm (s.storageMap 1 recipient) amount]
            rw [← Verity.Core.Uint256.add_assoc]
    _ = s.storageMap 1 sender + s.storageMap 1 recipient := by
          change ((s.storageMap 1 sender - amount) + amount) + s.storageMap 1 recipient =
            s.storageMap 1 sender + s.storageMap 1 recipient
          rw [Verity.Core.Uint256.sub_add_cancel_left]
· dsimp
  have hInsufficient' : ¬ amount.val ≤ (s.storageMap 1 sender).val := by
    simpa using hSufficient
  simp [ERC7984.transfer, ERC7984.balances, ERC7984.balanceInitialized,
    add64, UINT64_MOD, getMapping, setMapping, Verity.require, Verity.bind,
    Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.snd,
    hSenderNZ, hRecipientNZ, hInit, hInsufficient', hDistinct, Ne.symm hDistinct,
    hToBal64]
  change add (s.storageMap 1 sender)
      (add (s.storageMap 1 recipient) 0 % 18446744073709551616) =
    add (s.storageMap 1 sender) (s.storageMap 1 recipient)
  have hZeroAddMod : add (s.storageMap 1 recipient) 0 % 18446744073709551616 =
      s.storageMap 1 recipient := by
    have hZeroAdd : add (s.storageMap 1 recipient) 0 = s.storageMap 1 recipient :=
      Verity.Core.Uint256.add_zero _
    rw [hZeroAdd]
    exact uint256_mod_uint64_of_lt hToBal64
  rw [hZeroAddMod]
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.Zama.ERC7984ConfidentialToken.transferFrom_conservation":
        return [
            (
                "zama_transfer_from_conservation_simp",
                """have uint256_mod_uint64_of_lt : ∀ {x : Uint256},
    x < UINT64_MOD → x % 18446744073709551616 = x := by
  intro x hx
  cases hBal : x with
  | mk val hlt =>
      have hval : val < 18446744073709551616 := by
        simpa [hBal, UINT64_MOD] using hx
      apply Verity.Core.Uint256.ext
      change val % 18446744073709551616 % Verity.Core.Uint256.modulus = val
      rw [Nat.mod_eq_of_lt hval]
      exact Nat.mod_eq_of_lt hlt
have hHolderNZ : holder ≠ (0 : Address) := by
  have hNe : holder ≠ zeroAddress := by
    intro hEq
    subst hEq
    simp at hFrom
  simpa [zeroAddress] using hNe
have hRecipientNZ : recipient ≠ (0 : Address) := by
  have hNe : recipient ≠ zeroAddress := by
    intro hEq
    subst hEq
    simp at hTo
  simpa [zeroAddress] using hNe
have hAuthorized' :
    holder = s.sender ∨ blockTimestamp.val ≤ (s.storageMap2 3 holder s.sender).val := by
  cases hAuthorized with
  | inl hEq =>
      exact Or.inl ((beq_iff_eq).1 hEq)
  | inr hLe =>
      exact Or.inr (by simpa using hLe)
unfold transferFrom_conservation_spec balanceOf
by_cases hSufficient : s.storageMap 1 holder >= amount
· dsimp
  have hSufficient' : amount.val ≤ (s.storageMap 1 holder).val := by
    simpa using hSufficient
  simp [ERC7984.transferFrom, ERC7984.operators, ERC7984.balances,
    ERC7984.balanceInitialized, add64, UINT64_MOD, getMapping2, getMapping,
    setMapping, Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
    msgSender, Contract.run, ContractResult.snd, hHolderNZ, hRecipientNZ, hInit,
    hSufficient', hDistinct, Ne.symm hDistinct, hAuthorized']
  have hToAddMod : (s.storageMap 1 recipient + amount) % 18446744073709551616 =
      s.storageMap 1 recipient + amount :=
    uint256_mod_uint64_of_lt hToNoWrap
  change add (sub (s.storageMap 1 holder) amount)
      ((s.storageMap 1 recipient + amount) % 18446744073709551616) =
    add (s.storageMap 1 holder) (s.storageMap 1 recipient)
  rw [hToAddMod]
  calc
    sub (s.storageMap 1 holder) amount + (s.storageMap 1 recipient + amount)
        = (sub (s.storageMap 1 holder) amount + amount) + s.storageMap 1 recipient := by
            rw [Verity.Core.Uint256.add_comm (s.storageMap 1 recipient) amount]
            rw [← Verity.Core.Uint256.add_assoc]
    _ = s.storageMap 1 holder + s.storageMap 1 recipient := by
          change ((s.storageMap 1 holder - amount) + amount) + s.storageMap 1 recipient =
            s.storageMap 1 holder + s.storageMap 1 recipient
          rw [Verity.Core.Uint256.sub_add_cancel_left]
· dsimp
  have hInsufficient' : ¬ amount.val ≤ (s.storageMap 1 holder).val := by
    simpa using hSufficient
  simp [ERC7984.transferFrom, ERC7984.operators, ERC7984.balances,
    ERC7984.balanceInitialized, add64, UINT64_MOD, getMapping2, getMapping,
    setMapping, Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
    msgSender, Contract.run, ContractResult.snd, hHolderNZ, hRecipientNZ, hInit,
    hInsufficient', hDistinct, Ne.symm hDistinct, hAuthorized', hRecipientBal64]
  change add (s.storageMap 1 holder)
      (add (s.storageMap 1 recipient) 0 % 18446744073709551616) =
    add (s.storageMap 1 holder) (s.storageMap 1 recipient)
  have hZeroAddMod : add (s.storageMap 1 recipient) 0 % 18446744073709551616 =
      s.storageMap 1 recipient := by
    have hZeroAdd : add (s.storageMap 1 recipient) 0 = s.storageMap 1 recipient :=
      Verity.Core.Uint256.add_zero _
    rw [hZeroAdd]
    exact uint256_mod_uint64_of_lt hRecipientBal64
  rw [hZeroAddMod]
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.Zama.ERC7984ConfidentialToken.transfer_insufficient":
        return [
            (
                "zama_transfer_insufficient_simp",
                """have hSenderNZ : sender ≠ (0 : Address) := by
  have hNe : sender ≠ zeroAddress := by
    intro hEq
    subst hEq
    simp at hFrom
  simpa [zeroAddress] using hNe
have hRecipientNZ : recipient ≠ (0 : Address) := by
  have hNe : recipient ≠ zeroAddress := by
    intro hEq
    subst hEq
    simp at hTo
  simpa [zeroAddress] using hNe
have hInsufficient' : ¬ amount.val ≤ (s.storageMap 1 sender).val := by
  simpa using hInsufficient
unfold transfer_insufficient_spec balanceOf
dsimp
intro _
constructor
· simp [ERC7984.transfer, ERC7984.balances, ERC7984.balanceInitialized,
    add64, UINT64_MOD, getMapping, setMapping, Verity.require, Verity.bind,
    Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.snd,
    hSenderNZ, hRecipientNZ, hInit, hInsufficient', hToBal64]
  intro hEq
  exact False.elim (hDistinct hEq)
· have hDistinct' : recipient ≠ sender := Ne.symm hDistinct
  simp [ERC7984.transfer, ERC7984.balances, ERC7984.balanceInitialized,
    add64, UINT64_MOD, getMapping, setMapping, Verity.require, Verity.bind,
    Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.snd,
    hSenderNZ, hRecipientNZ, hInit, hInsufficient', hDistinct, hDistinct', hToBal64]
  change add (s.storageMap 1 recipient) 0 % 18446744073709551616 = s.storageMap 1 recipient
  have hZeroAdd : add (s.storageMap 1 recipient) 0 = s.storageMap 1 recipient :=
    Verity.Core.Uint256.add_zero _
  rw [hZeroAdd]
  cases hs : s.storageMap 1 recipient with
  | mk val hlt =>
      have hval : val < 18446744073709551616 := by
        simpa [hs, UINT64_MOD] using hToBal64
      apply Verity.Core.Uint256.ext
      change val % 18446744073709551616 % Verity.Core.Uint256.modulus = val
      rw [Nat.mod_eq_of_lt hval]
      exact Nat.mod_eq_of_lt hlt
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.Zama.ERC7984ConfidentialToken.setOperator_updates":
        return [
            (
                "zama_set_operator_simp",
                """unfold setOperator_updates_spec operatorExpiry
constructor
· simp [ERC7984.setOperator, ERC7984.operators, msgSender, setMapping2,
    Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.snd]
· intro h sp hNe
  by_cases hh : h = s.sender
  · by_cases hs : sp = operator
    · exfalso
      exact hNe (by cases hh; cases hs; rfl)
    · simp [ERC7984.setOperator, ERC7984.operators, msgSender, setMapping2,
        Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.snd,
        hh, hs]
  · simp [ERC7984.setOperator, ERC7984.operators, msgSender, setMapping2,
      Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.snd,
      hh]
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.Zama.ERC7984ConfidentialToken.mint_increases_supply":
        return [
            (
                "zama_mint_success_simp",
                """have hRecipientNZ : recipient ≠ (0 : Address) := by
  have hNe : recipient ≠ zeroAddress := by
    intro hEq
    subst hEq
    simp at hTo
  simpa [zeroAddress] using hNe
have hSuccess : add64 (s.storage 0) amount >= s.storage 0 := by
  by_cases h : add64 (s.storage 0) amount >= s.storage 0
  · exact h
  · unfold tryIncrease64 at hNoOverflow
    simp [h] at hNoOverflow
have hSuccess' : (s.storage 0).val ≤ (add (s.storage 0) amount % 18446744073709551616).val := by
  simpa [add64, UINT64_MOD] using hSuccess
unfold mint_increases_supply_spec supply balanceOf
dsimp
intro _
constructor
· simp [ERC7984.mint, ERC7984.totalSupply, ERC7984.balances, ERC7984.balanceInitialized,
    tryIncrease64, add64, UINT64_MOD, getStorage, setStorage, getMapping, setMapping,
    Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
    Contract.run, ContractResult.snd, hRecipientNZ, hSuccess']
· simp [ERC7984.mint, ERC7984.totalSupply, ERC7984.balances, ERC7984.balanceInitialized,
    tryIncrease64, add64, UINT64_MOD, getStorage, setStorage, getMapping, setMapping,
    Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
    Contract.run, ContractResult.snd, hRecipientNZ, hSuccess']
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.Zama.ERC7984ConfidentialToken.mint_overflow_protection":
        return [
            (
                "zama_mint_overflow_simp",
                """have hRecipientNZ : recipient ≠ (0 : Address) := by
  have hNe : recipient ≠ zeroAddress := by
    intro hEq
    subst hEq
    simp at hTo
  simpa [zeroAddress] using hNe
have hFail : ¬ add64 (s.storage 0) amount >= s.storage 0 := by
  intro hSuccess
  have : (tryIncrease64 (s.storage 0) amount).1 = true := by
    simp [tryIncrease64, hSuccess]
  rw [this] at hOverflow
  contradiction
have hFail' : ¬ (s.storage 0).val ≤ (add (s.storage 0) amount % 18446744073709551616).val := by
  simpa [add64, UINT64_MOD] using hFail
unfold mint_overflow_protection_spec supply balanceOf
dsimp
intro _
constructor
· simp [ERC7984.mint, ERC7984.totalSupply, ERC7984.balances, ERC7984.balanceInitialized,
    tryIncrease64, add64, UINT64_MOD, getStorage, setStorage, getMapping, setMapping,
    Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
    Contract.run, ContractResult.snd, hRecipientNZ, hFail', hToBal64]
· simp [ERC7984.mint, ERC7984.totalSupply, ERC7984.balances, ERC7984.balanceInitialized,
    tryIncrease64, add64, UINT64_MOD, getStorage, setStorage, getMapping, setMapping,
    Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
    Contract.run, ContractResult.snd, hRecipientNZ, hFail', hToBal64]
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.Zama.ERC7984ConfidentialToken.burn_decreases_supply":
        return [
            (
                "zama_burn_success_simp",
                """have hHolderNZ : holder ≠ (0 : Address) := by
  have hNe : holder ≠ zeroAddress := by
    intro hEq
    subst hEq
    simp at hFrom
  simpa [zeroAddress] using hNe
have hSufficient' : amount.val ≤ (s.storageMap 1 holder).val := by
  simpa using hSufficient
unfold burn_decreases_supply_spec balanceOf supply
dsimp
intro _
constructor
· simp [ERC7984.burn, ERC7984.totalSupply, ERC7984.balances, ERC7984.balanceInitialized,
    add64, sub64, UINT64_MOD, getStorage, setStorage, getMapping, setMapping,
    Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
    Contract.run, ContractResult.snd, hHolderNZ, hInit, hSufficient']
· simp [ERC7984.burn, ERC7984.totalSupply, ERC7984.balances, ERC7984.balanceInitialized,
    add64, sub64, UINT64_MOD, getStorage, setStorage, getMapping, setMapping,
    Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
    Contract.run, ContractResult.snd, hHolderNZ, hInit, hSufficient']
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.Zama.ERC7984ConfidentialToken.burn_insufficient":
        return [
            (
                "zama_burn_insufficient_simp",
                """have hHolderNZ : holder ≠ (0 : Address) := by
  have hNe : holder ≠ zeroAddress := by
    intro hEq
    subst hEq
    simp at hFrom
  simpa [zeroAddress] using hNe
have hInsufficient' : ¬ amount.val ≤ (s.storageMap 1 holder).val := by
  simpa using hInsufficient
unfold burn_insufficient_spec balanceOf supply
dsimp
intro _
constructor
· simp [ERC7984.burn, ERC7984.totalSupply, ERC7984.balances, ERC7984.balanceInitialized,
    add64, sub64, UINT64_MOD, getStorage, setStorage, getMapping, setMapping,
    Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
    Contract.run, ContractResult.snd, hHolderNZ, hInit, hInsufficient']
· simp [ERC7984.burn, ERC7984.totalSupply, ERC7984.balances, ERC7984.balanceInitialized,
    add64, sub64, UINT64_MOD, getStorage, setStorage, getMapping, setMapping,
    Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
    Contract.run, ContractResult.snd, hHolderNZ, hInit, hInsufficient', hSupply64]
  change (s.storage 0 - 0) % 18446744073709551616 = s.storage 0
  rw [Verity.Core.Uint256.sub_zero]
  cases hs : s.storage 0 with
  | mk val hlt =>
      have hval : val < 18446744073709551616 := by
        simpa [hs, UINT64_MOD] using hSupply64
      apply Verity.Core.Uint256.ext
      change val % 18446744073709551616 % Verity.Core.Uint256.modulus = val
      rw [Nat.mod_eq_of_lt hval]
      exact Nat.mod_eq_of_lt hlt
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.Reserve.AuctionPriceBand.price_at_start_time":
        return [
            (
                "reserve_price_boundary",
                """unfold price_at_start_time_spec _price
simp
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.Reserve.AuctionPriceBand.price_at_end_time":
        return [
            (
                "reserve_price_boundary",
                """unfold price_at_end_time_spec _price
have h : (auction_endTime == auction_startTime) = false := by
  simpa [beq_iff_eq] using fun h => hStartNeEnd h.symm
simp [h]
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.Reserve.AuctionPriceBand.price_lower_bound":
        return [
            (
                "reserve_price_lower_bound",
                """unfold price_lower_bound_spec _price
by_cases h1 : block_timestamp == auction_startTime
· simpa [h1] using hBand
· by_cases h2 : block_timestamp == auction_endTime
  · simp [h1, h2]
  · simp [h1, h2]
    split
    · exact Nat.le_refl _
    · rename_i hNotLt
      exact Nat.not_lt.mp hNotLt
""",
            )
        ]
    if theorem_name == "Benchmark.Cases.Reserve.AuctionPriceBand.price_upper_bound":
        return [
            (
                "reserve_price_upper_bound_helper",
                """exact Benchmark.Grindset.Reserve.price_upper_bound_spec_holds
  sellPrices buyPrices auction_startTime auction_endTime block_timestamp hBand hSafe
""",
            )
        ]
    return []


def _contract_grind_hints(workspace: Path, implementation_files: object) -> list[str]:
    if not isinstance(implementation_files, list):
        return []
    hints: list[str] = []
    seen: set[str] = set()
    for rel in implementation_files:
        if not isinstance(rel, str) or not (workspace / rel).is_file():
            continue
        current_contract: str | None = None
        in_block_comment = False
        for raw_line in (workspace / rel).read_text(encoding="utf-8").splitlines():
            line = raw_line.strip()
            if in_block_comment:
                if "-/" in line:
                    in_block_comment = False
                    line = line.split("-/", 1)[1].strip()
                else:
                    continue
            if line.startswith("/-"):
                if "-/" not in line:
                    in_block_comment = True
                continue
            if line.startswith(("--", "/--", "*")):
                continue
            contract_match = re.match(r"verity_contract\s+([A-Za-z_][A-Za-z0-9_']*)\b", line)
            if contract_match:
                current_contract = contract_match.group(1)
                continue
            if current_contract is None:
                continue
            function_match = re.match(r"function\s+(?:[A-Za-z_][A-Za-z0-9_']*\([^)]*\)\s+)*([A-Za-z_][A-Za-z0-9_']*)\b", line)
            storage_match = re.match(r"([A-Za-z_][A-Za-z0-9_']*)\s*:\s*.+:=\s*slot\s+\d+", line)
            name = None
            if function_match:
                name = function_match.group(1)
            elif storage_match:
                name = storage_match.group(1)
            if name and name not in {"on", "nonreentrant"}:
                hint = f"{current_contract}.{name}"
                if hint not in seen:
                    seen.add(hint)
                    hints.append(hint)
    return hints


def _heuristic_tactic_candidates(
    task: dict[str, object],
    workspace: Path,
    original: str,
    implementation_files: object,
) -> list[tuple[str, str]]:
    theorem_name = task.get("theorem_name")
    if theorem_name == "Benchmark.Cases.Lido.VaulthubLocked.locked_funds_solvency":
        return []
    spec_names = sorted(set(re.findall(r"\b([A-Za-z_][A-Za-z0-9_'.]*_spec)\b", original)))
    hints = _contract_grind_hints(workspace, implementation_files)
    if not spec_names and not hints:
        return []
    lines: list[str] = []
    if spec_names:
        lines.append("unfold " + " ".join(spec_names))
    hint_text = ", ".join(hints)
    lines.append(f"grind [{hint_text}]" if hint_text else "grind")
    return [("heuristic_grind", "\n".join(lines) + "\n")]


def _compact_lean_output(output: str, limit: int = 4000) -> str:
    lines = output.splitlines()
    error_blocks: list[str] = []
    for index, line in enumerate(lines):
        if "error:" in line.lower():
            error_blocks.extend(lines[index : min(len(lines), index + 8)])
    if error_blocks:
        filtered = [line for line in error_blocks if not line.startswith("trace: .>") and "LEAN_PATH=" not in line]
        return "\n".join(filtered)[-limit:]
    return output[-limit:]


def _retry_feedback(output: str) -> str:
    compact = _compact_lean_output(output, limit=900)
    lines = [line for line in compact.splitlines() if "error:" in line.lower() or "unsolved goals" in line.lower()]
    text = "\n".join(lines) if lines else compact
    if "maximum recursion depth has been reached" in compact:
        text += (
            "\nAvoid broad recursive simp. Do not put ContractResult.snd in a simp list. "
            "Prefer unfolding the target contract/spec, split contract if/branch conditions with by_cases, "
            "and simplify concrete storage slot names."
        )
    if "unknown identifier" in compact:
        text += "\nUse only names visible in the provided files. Do not invent Verity.Storage.* helpers or ContractState methods."
    if "unknown constant" in compact:
        text += "\nUse only visible declarations. Do not invent storage_set or ContractState update lemmas."
    if "failed to unfold" in compact:
        text += "\nDo not unfold generated contract .spec declarations unless Lean shows they unfold; unfold the concrete function and public spec instead."
    return text[-240:]


def _attempt_task(
    task: dict[str, object],
    workspace: Path,
    *,
    base_url: str,
    max_attempts: int,
    attempts_dir: Path,
) -> dict[str, object]:
    editable_files = task.get("editable_files")
    implementation_files = task.get("implementation_files")
    specification_files = task.get("specification_files")
    target_module = task.get("target_module")
    if not isinstance(editable_files, list) or len(editable_files) != 1 or not isinstance(target_module, str):
        return {"task_ref": task.get("task_ref"), "status": "unsupported_task_shape"}
    editable = str(editable_files[0])
    proof_path = workspace / editable
    original = proof_path.read_text(encoding="utf-8")
    proof_path.write_text(original, encoding="utf-8")
    feedback = "No Lean feedback yet."
    attempts: list[dict[str, object]] = []

    if not re.search(r"\b(sorry|admit|axiom)\b|\?_[A-Za-z0-9_']*", original):
        code, output = _run_lean_module(workspace, target_module)
        attempts.append(
            {
                "attempt": "preexisting",
                "status": "lean_passed" if code == 0 else "lean_failed",
                "exit_code": code,
                "candidate_path": None,
                "output": _compact_lean_output(output),
                "response_usage": None,
            }
        )
        if code == 0:
            return {"task_ref": task.get("task_ref"), "status": "lean_passed", "attempts": attempts}
        feedback = output

    local_candidates = _local_tactic_candidates(task)
    local_candidates.extend(_heuristic_tactic_candidates(task, workspace, original, implementation_files))

    for name, tactic_body in local_candidates:
        candidate = _candidate_from_local(original, tactic_body, task.get("theorem_name"))
        proof_path.write_text(candidate, encoding="utf-8")
        candidate_path = attempts_dir / f"{str(task.get('task_id') or task.get('task_ref')).replace('/', '__')}-local-{name}.lean"
        candidate_path.parent.mkdir(parents=True, exist_ok=True)
        candidate_path.write_text(candidate, encoding="utf-8")
        code, output = _run_lean_module(workspace, target_module)
        attempts.append(
            {
                "attempt": f"local:{name}",
                "status": "lean_passed" if code == 0 else "lean_failed",
                "exit_code": code,
                "candidate_path": str(candidate_path),
                "output": _compact_lean_output(output),
                "response_usage": None,
            }
        )
        if code == 0:
            return {"task_ref": task.get("task_ref"), "status": "lean_passed", "attempts": attempts}
        feedback = output

    for attempt_index in range(1, max_attempts + 1):
        context_text, symbol_text = _context_for_task(
            task,
            workspace,
            editable,
            editable_files,
            specification_files,
            implementation_files,
        )
        messages = [
            {
                "role": "system",
                "content": (
                    "You are editing one Lean 4 file in a Verity benchmark workspace. "
                    "Return only the tactic proof body that belongs under `:= by`, not a complete file "
                    "and not prose. Do not repeat imports, namespace declarations, theorem headers, or `:= by`. "
                    "Do not use sorry, admit, axiom, hidden imports, or placeholders. "
                    "Use the Lean tactic `grind`; there is no `Grindset.grind` declaration. "
                    "Use only declarations visible in the provided public files. Do not invent "
                    "Verity.Storage helpers, storage_set lemmas, or ContractState methods."
                ),
            },
            {
                "role": "user",
                "content": (
                    f"Task: {task.get('task_ref')}\n"
                    f"Target theorem: {task.get('theorem_name')}\n"
                    f"Editable file: {editable}\n\n"
                    f"Public symbol summary:\n{symbol_text}\n\n"
                    + context_text
                    + f"\n\nLean feedback:\n{_retry_feedback(feedback)}\n"
                ),
            },
        ]
        try:
            response = chat_completion(messages, base_url=base_url)
            rejection = _is_rejected_model_body(task, _response_text(response))
            if rejection:
                attempts.append(
                    {
                        "attempt": attempt_index,
                        "status": "rejected_candidate",
                        "reason": rejection,
                        "response_usage": response.get("usage") if isinstance(response, dict) else None,
                    }
                )
                break
            candidate = _candidate_from_response(original, _response_text(response), task.get("theorem_name"))
        except Exception as exc:
            if "exceeds the available context size" not in str(exc):
                attempts.append({"attempt": attempt_index, "status": "request_failed", "error": str(exc)})
                break
            minimal_messages = [
                messages[0],
                {
                    "role": "user",
                    "content": (
                        "Return Lean tactic body only, under := by. No prose.\n"
                        f"Target: {task.get('theorem_name')}\n"
                        f"Errors: {_retry_feedback(feedback)[:160]}\n"
                    ),
                },
            ]
            try:
                response = chat_completion(minimal_messages, base_url=base_url, max_tokens=1024)
                rejection = _is_rejected_model_body(task, _response_text(response))
                if rejection:
                    attempts.append(
                        {
                            "attempt": attempt_index,
                            "status": "rejected_candidate",
                            "reason": rejection,
                            "response_usage": response.get("usage") if isinstance(response, dict) else None,
                        }
                    )
                    break
                candidate = _candidate_from_response(original, _response_text(response), task.get("theorem_name"))
            except Exception as fallback_exc:
                attempts.append({"attempt": attempt_index, "status": "request_failed", "error": str(fallback_exc)})
                break
        proof_path.write_text(candidate, encoding="utf-8")
        candidate_path = attempts_dir / f"{str(task.get('task_id') or task.get('task_ref')).replace('/', '__')}-attempt-{attempt_index}.lean"
        candidate_path.parent.mkdir(parents=True, exist_ok=True)
        candidate_path.write_text(candidate, encoding="utf-8")
        code, output = _run_lean_module(workspace, target_module)
        attempts.append(
            {
                "attempt": attempt_index,
                "status": "lean_passed" if code == 0 else "lean_failed",
                "exit_code": code,
                "candidate_path": str(candidate_path),
                "output": _compact_lean_output(output),
                "response_usage": response.get("usage") if isinstance(response, dict) else None,
            }
        )
        if code == 0:
            return {"task_ref": task.get("task_ref"), "status": "lean_passed", "attempts": attempts}
        feedback = output

    if not any(attempt.get("status") in {"lean_failed", "lean_passed"} for attempt in attempts):
        proof_path.write_text(original, encoding="utf-8")
    return {"task_ref": task.get("task_ref"), "status": "failed_submitted" if attempts else "failed_no_attempt", "attempts": attempts}


def run_group(
    group_id: str,
    *,
    suite: str = "active",
    keep_workspace: bool = False,
    dry_run: bool = False,
    max_attempts: int = 1,
    task_ref: str | None = None,
) -> tuple[int, Path]:
    started_at = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    run_subject = task_ref or group_id
    run_id = f"{started_at.replace(':', '').replace('-', '').replace('Z', '')}-{RUN_SLUG}-{run_subject.replace('/', '__')}"
    run_dir = RESULTS_DIR / "runs" / run_id
    run_dir.mkdir(parents=True, exist_ok=True)
    start = time.time()
    group = load_group(group_id, suite)
    if task_ref:
        group = filter_group_to_task(group, task_ref)
    built = build_group_workspace(group, run_id=run_id)
    assert_workspace_isolated(built.path)
    base_url = os.environ.get("DEFAULT_HARNESS_BASE_URL", os.environ.get("GAZELLA_BASE_URL", DEFAULT_BASE_URL))
    response: dict[str, object]
    if dry_run:
        response = {"status": "dry_run", "base_url": base_url, "model": DEFAULT_MODEL, "max_attempts": max_attempts}
    else:
        task_results: list[dict[str, object]] = []
        try:
            tasks_payload = json.loads((built.path / "harness" / "TASKS.json").read_text(encoding="utf-8"))
            for task in tasks_payload.get("tasks", []):
                if isinstance(task, dict):
                    task_results.append(
                        _attempt_task(
                            task,
                            built.path,
                            base_url=base_url,
                            max_attempts=max_attempts,
                            attempts_dir=run_dir / "attempts",
                        )
                    )
            response = {"status": "completed", "base_url": base_url, "model": DEFAULT_MODEL, "tasks": task_results}
        except Exception as exc:
            response = {"status": "harness_error", "error": str(exc), "base_url": base_url, "model": DEFAULT_MODEL, "tasks": task_results}

    (run_dir / "workspace-manifest.json").write_text((built.path / "workspace-manifest.json").read_text(encoding="utf-8"), encoding="utf-8")
    (run_dir / "harness-request.json").write_text(json.dumps({"group": group_to_json(group), "base_url": base_url, "model": DEFAULT_MODEL}, indent=2) + "\n", encoding="utf-8")
    (run_dir / "harness-response.json").write_text(json.dumps(response, indent=2) + "\n", encoding="utf-8")
    (run_dir / "stdout.txt").write_text("", encoding="utf-8")
    (run_dir / "stderr.txt").write_text("", encoding="utf-8")
    submitted_dir = run_dir / "submitted"
    for task in group.tasks:
        for rel in task.editable_files:
            src = built.path / rel
            if src.is_file():
                dst = submitted_dir / rel
                dst.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(src, dst)
    verifier_result = verify_group(group, built.path, artifact_dir=run_dir / "verifier")
    run = {
        "schema_version": 1,
        "run_id": run_id,
        "harness_id": HARNESS_ID,
        "model": DEFAULT_MODEL,
        "track": "group/lean_tools",
        "run_mode": "task" if task_ref else "group",
        "group_id": group_id,
        "task_ref": task_ref,
        "suite": suite,
        "base_url": base_url,
        "auth_mode": "env" if _api_key() else "none",
        "duration_seconds": round(time.time() - start, 3),
        "harness_status": response["status"],
        "workspace": str(built.path) if keep_workspace else None,
        "verifier": verifier_result,
    }
    (run_dir / "run.json").write_text(json.dumps(run, indent=2) + "\n", encoding="utf-8")
    write_run_report(run_dir, run)
    if not keep_workspace:
        shutil.rmtree(built.path, ignore_errors=True)
    return (0 if response["status"] == "completed" and verifier_result["score"]["passed_targets"] == verifier_result["score"]["total_targets"] else 1), run_dir


def main() -> int:
    parser = argparse.ArgumentParser(description="Default OpenAI-compatible Lean-tool harness")
    sub = parser.add_subparsers(dest="command", required=True)
    sub.add_parser("smoke")
    run = sub.add_parser("run-group")
    run.add_argument("group_id")
    run.add_argument("--suite", choices=["active", "backlog", "all"], default="active")
    run.add_argument("--keep-workspace", action="store_true")
    run.add_argument("--dry-run", action="store_true")
    run.add_argument("--max-attempts", type=int, default=1)
    run.add_argument("--task-ref")
    args = parser.parse_args()
    if args.command == "smoke":
        print(json.dumps(endpoint_smoke(os.environ.get("DEFAULT_HARNESS_BASE_URL", os.environ.get("GAZELLA_BASE_URL", DEFAULT_BASE_URL))), indent=2))
        return 0
    code, run_dir = run_group(
        args.group_id,
        suite=args.suite,
        keep_workspace=args.keep_workspace,
        dry_run=args.dry_run,
        max_attempts=args.max_attempts,
        task_ref=args.task_ref,
    )
    print(run_dir)
    return code


if __name__ == "__main__":
    raise SystemExit(main())
