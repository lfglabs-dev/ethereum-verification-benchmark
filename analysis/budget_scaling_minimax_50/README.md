# Budget Scaling Experiment: minimax/minimax-m3 on 50 tasks

Selection rule:
- 38 tasks were solved by Minimax in the current v0.1 local summaries.
- The selected panel starts with those Minimax-solved tasks sorted by observed total tokens.
- It is topped up to 50 with GPT 5.5-only solved tasks; available GPT-only pool: 29.

Recommended graph:
- x: budget profile
- y: cumulative solve rate
- bars or annotations: newly solved tasks at each profile
- secondary x or separate plot: cumulative total tokens / completion tokens

Generated after cascade execution:
- `cascade_summary.csv/json`: cumulative solves plus prompt/completion/total token effort.
- `cascade_solve_rate.svg`: x = budget profile, y = cumulative solve rate.
- `cascade_effort_solve_rate.svg`: x = cumulative total tokens, y = cumulative solve rate.

Harness note:
- For `--harness default`, the effective proof-search knobs are `max_attempts` and `max_tool_calls`.
- `max_turns` and `shell_timeout_seconds` are still recorded in the profile so the same ladder can be reused for shell-agent harnesses, where those knobs are binding.

Run cascade:
```bash
python3 scripts/plan_budget_scaling_experiment.py --execute --jobs 4
```

For the official MiniMax OpenAI-compatible endpoint, pass the base URL and model explicitly:
```bash
DEFAULT_HARNESS_API_KEY=... python3 scripts/plan_budget_scaling_experiment.py --execute --jobs 4 --base-url https://api.minimax.io/v1 --model MiniMax-M3
```

The cascade executes each profile only on tasks not solved by earlier profiles.
Use `commands_full_matrix.sh` only for independent budget scaling where every profile is evaluated from scratch.
