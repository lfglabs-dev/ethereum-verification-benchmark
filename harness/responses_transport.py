"""Generic opt-in OpenAI Responses API transport with task-local state."""
from __future__ import annotations
import json, os, urllib.error, urllib.request
from dataclasses import dataclass
from typing import Any
from harness.transport_errors import ChatCompletionError

DEFAULT_WIRE_API = os.environ.get("DEFAULT_HARNESS_WIRE_API", "chat_completions").strip().lower()
if DEFAULT_WIRE_API not in {"chat_completions", "responses"}:
    raise ValueError("DEFAULT_HARNESS_WIRE_API must be chat_completions or responses")

@dataclass
class ResponsesState:
    previous_response_id: str | None = None
    cursor: int = 0
    resets: int = 0
    last_reset_reason: str | None = None
    def reset(self, reason: str) -> None:
        self.previous_response_id = None; self.cursor = 0; self.resets += 1; self.last_reset_reason = reason

def _flat_tools(tools: list[dict[str, Any]] | None) -> list[dict[str, Any]]:
    out=[]
    for tool in tools or []:
        fn=tool.get("function") if isinstance(tool,dict) else None
        if not isinstance(fn,dict) or not isinstance(fn.get("name"),str): raise ValueError("malformed function tool")
        out.append({"type":"function", **fn})
    return out

def _inputs(messages: list[dict[str,Any]], state: ResponsesState) -> list[dict[str,Any]]:
    source=messages[state.cursor:] if state.previous_response_id and len(messages)>=state.cursor else messages
    if state.previous_response_id is None: state.cursor=0
    out=[]
    for m in source:
        role=m.get("role"); content=m.get("content")
        if role=="assistant" and state.previous_response_id: continue
        if role=="tool":
            cid=m.get("tool_call_id")
            if not isinstance(cid,str) or not (1<=len(cid)<=64): raise ValueError("Responses requires matching 1-64 char call_id")
            out.append({"type":"function_call_output","call_id":cid,"output":str(content or "")})
        elif role in {"system","developer","user"} and isinstance(content,str):
            out.append({"role":"developer" if role=="system" else role,"content":[{"type":"input_text","text":content}]})
        elif role=="assistant" and isinstance(content,str) and content:
            out.append({"role":"assistant","content":[{"type":"output_text","text":content}]})
    return out

def responses_completion(messages: list[dict[str,Any]], *, state: ResponsesState, model: str, tools: list[dict[str,Any]]|None=None) -> dict[str,Any]:
    key=os.environ.get("DEFAULT_HARNESS_RESPONSES_API_KEY","")
    if not key: raise ChatCompletionError("missing Responses API credential",kind="provider_setup_error",attempts=0,timeout_seconds=0,transient=False)
    base=os.environ.get("DEFAULT_HARNESS_RESPONSES_BASE_URL","https://api.meta.ai/v1").rstrip('/')
    payload={"model":model,"input":_inputs(messages,state),"tools":_flat_tools(tools),"tool_choice":"auto","reasoning":{"effort":os.environ.get("DEFAULT_HARNESS_REASONING_EFFORT","minimal")},"max_output_tokens":max(256,int(os.environ.get("DEFAULT_HARNESS_MAX_RESPONSE_TOKENS","8192"))),"store":True}
    if state.previous_response_id: payload["previous_response_id"]=state.previous_response_id
    req=urllib.request.Request(base+"/responses",data=json.dumps(payload).encode(),headers={"Authorization":"Bearer "+key,"Content-Type":"application/json"})
    try:
        with urllib.request.urlopen(req,timeout=300) as r: d=json.load(r)
    except urllib.error.HTTPError as e:
        detail=e.read().decode(errors="replace"); raise ChatCompletionError(f"Responses HTTP {e.code}: {detail[:1200]}",kind="http_error",attempts=1,timeout_seconds=300,transient=e.code in {408,409,429} or e.code>=500,last_status=e.code) from e
    rid=d.get("id")
    if not isinstance(rid,str) or not rid: raise ChatCompletionError("Responses missing id",kind="protocol_error",attempts=1,timeout_seconds=300,transient=False)
    state.previous_response_id=rid; state.cursor=len(messages)
    text=[]; calls=[]
    for item in d.get("output") or []:
        if not isinstance(item,dict): continue
        if item.get("type")=="function_call":
            cid=item.get("call_id")
            if not isinstance(cid,str) or not (1<=len(cid)<=64): raise ChatCompletionError("Responses invalid call_id",kind="protocol_error",attempts=1,timeout_seconds=300,transient=False)
            calls.append({"id":cid,"type":"function","function":{"name":item.get("name"),"arguments":item.get("arguments") or "{}"}})
        elif item.get("type")=="message":
            text += [p["text"] for p in item.get("content") or [] if isinstance(p,dict) and p.get("type")=="output_text" and isinstance(p.get("text"),str)]
    u=d.get("usage") or {}; msg={"role":"assistant","content":"\n".join(text) or None}
    if calls: msg["tool_calls"]=calls
    return {"id":rid,"choices":[{"index":0,"message":msg,"finish_reason":"tool_calls" if calls else "stop"}],"usage":{"prompt_tokens":int(u.get("input_tokens",0) or 0),"completion_tokens":int(u.get("output_tokens",0) or 0),"total_tokens":int(u.get("total_tokens",0) or 0)},"wire_api":"responses","responses_state":{"previous_response_id":payload.get("previous_response_id"),"resets":state.resets,"last_reset_reason":state.last_reset_reason}}

def responses_preflight(model: str) -> dict[str,Any]:
    state=ResponsesState(); tools=[{"type":"function","function":{"name":"preflight_echo","description":"Echo a value; call this tool when requested.","parameters":{"type":"object","properties":{"value":{"type":"string"}},"required":["value"],"additionalProperties":False}}}]
    messages=[{"role":"developer","content":"You must call preflight_echo; do not answer in text."},{"role":"user","content":"Call preflight_echo now with value ok."}]
    first=responses_completion(messages,state=state,model=model,tools=tools)
    calls=first["choices"][0]["message"].get("tool_calls") or []
    if not calls: return {"status":"failed","checks":{"responses":True,"tool_calls":False,"previous_response_id":False,"usage_accounting":bool(first.get("usage"))}}
    call=calls[0]; messages.extend([first["choices"][0]["message"],{"role":"tool","tool_call_id":call["id"],"content":'{"value":"ok"}'}]); second=responses_completion(messages,state=state,model=model,tools=tools)
    usage={k:int(first["usage"].get(k,0))+int(second["usage"].get(k,0)) for k in ("prompt_tokens","completion_tokens","total_tokens")}; usage["requests"]=2
    return {"status":"passed","model":model,"wire_api":"responses","checks":{"responses":True,"tool_calls":True,"previous_response_id":second["responses_state"]["previous_response_id"]==first["id"],"usage_accounting":usage["total_tokens"]>0},"usage":usage}
