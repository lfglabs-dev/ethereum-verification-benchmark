import json
from unittest import mock
from harness.responses_transport import ResponsesState, _flat_tools, responses_completion

class Resp:
 def __init__(self,d): self.d=d
 def __enter__(self): return self
 def __exit__(self,*a): return False
 def read(self): return json.dumps(self.d).encode()

def test_two_turn_previous_response_id(monkeypatch):
 monkeypatch.setenv('DEFAULT_HARNESS_RESPONSES_API_KEY','x')
 payloads=[]; replies=[
  {'id':'resp1','output':[{'type':'function_call','call_id':'call1','name':'echo','arguments':'{"value":"ok"}'}],'usage':{'input_tokens':1,'output_tokens':2,'total_tokens':3}},
  {'id':'resp2','output':[{'type':'message','content':[{'type':'output_text','text':'done'}]}],'usage':{'input_tokens':1,'output_tokens':1,'total_tokens':2}}]
 def open_(req,timeout): payloads.append(json.loads(req.data)); return Resp(replies.pop(0))
 state=ResponsesState(); msgs=[{'role':'system','content':'Use echo'},{'role':'user','content':'echo ok'}]; tools=[{'type':'function','function':{'name':'echo','parameters':{'type':'object'}}}]
 with mock.patch('harness.responses_transport.urllib.request.urlopen',side_effect=open_):
  a=responses_completion(msgs,state=state,model='muse',tools=tools); tc=a['choices'][0]['message']['tool_calls'][0]; msgs += [a['choices'][0]['message'],{'role':'tool','tool_call_id':tc['id'],'content':'ok'}]; b=responses_completion(msgs,state=state,model='muse',tools=tools)
 assert payloads[1]['previous_response_id']=='resp1'; assert payloads[1]['input']==[{'type':'function_call_output','call_id':'call1','output':'ok'}]; assert b['choices'][0]['message']['content']=='done'

def test_reset_forces_fresh_history():
 s=ResponsesState('old',4); s.reset('compaction'); assert s.previous_response_id is None and s.cursor==0 and s.resets==1
