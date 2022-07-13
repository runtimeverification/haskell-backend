#!/usr/bin/env python3
from re import sub
from jsonrpcclient import request, request_uuid, notification, parse_json, Ok
import json, socket, os, subprocess, time

HOST = "127.0.0.1"  # Standard loopback interface address (localhost)
PORT = 31337  # Port to listen on (non-privileged ports are > 1023)
CREATE_MISSING_GOLDEN = os.getenv("CREATE_MISSING_GOLDEN", 'False').lower() in ('true', '1', 't')


def recv_all(sock):
    BUFF_SIZE = 4096 # 4 KiB
    data = b''
    while True:
        part = sock.recv(BUFF_SIZE)
        data += part
        if len(part) < BUFF_SIZE:
            # either 0 or end of data
            break
    return data


def rpc_request_id1(name, params):
    return json.dumps(
            request(
                name,
                params=params,
                id=1)
        ).encode()


def execute(state, max_depth=None, halt_patterns=[]):
    return json.dumps(
            request(
                "execute",
                params={
                    "state": state,
                    "max-depth": max_depth,
                    "halt-patterns": halt_patterns
                })
        ).encode()


def step(state):
    return json.dumps(request_uuid("step", params={"state": state})).encode()


def implies(antecedent, consequent):
    return json.dumps(
            request_uuid(
                "implies",
                params={
                    "antecedent": antecedent,
                    "consequent": consequent
                })
        ).encode()

def simplify(state):
    return json.dumps(request_uuid("simplify", params={"state": state})).encode()


def cancel():
    return json.dumps(notification("cancel")).encode()




print("Running execute tests:")

for name in os.listdir("./execute"):
  print(f"Running test '{name}'...")
  def_path = os.path.join("./execute", name, "definition.kore")
  req_json_path = os.path.join("./execute", name, "request.json")
  req_kore_path = os.path.join("./execute", name, "request.kore")
  resp_golden_path = os.path.join("./execute", name, "response.golden")
  with open(req_json_path, 'r') as req_json_raw:
    with open(req_kore_path, 'r') as req_kore_raw:
      req = json.loads(req_json_raw.read())
      req["state"] = req_kore_raw.read();

      with subprocess.Popen(f"kore-rpc {def_path} --module CONTROL-FLOW --server-port {PORT}".split()) as process:
        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
          while True:
            try:
              s.connect((HOST, PORT))
              print("Connected to server...")
              break
            except:
              pass
          s.sendall(rpc_request_id1("execute", req))
          resp = recv_all(s)
          process.kill()
          print(resp)

          if os.path.exists(resp_golden_path):
            print("Checking against golden file...")
            with open(resp_golden_path, 'rb') as resp_golden_raw:
              golden_json = resp_golden_raw.read()
              if golden_json != resp:
                print(f"Test '{name}' failed...")
                exit(1)
              else:
                print(f"Test '{name}' passed...")
          elif CREATE_MISSING_GOLDEN:
            with open(resp_golden_path, 'wb') as resp_golden_writer:
               resp_golden_writer.write(resp)
          else:
            print("Golden file not found...")
            exit(1)



