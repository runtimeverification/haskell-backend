#!/usr/bin/env python3
from jsonrpcclient import request, request_uuid, notification
import json, socket, os, subprocess, difflib

HOST = "127.0.0.1"  # Standard loopback interface address (localhost)
PORT = 31337  # Port to listen on (non-privileged ports are > 1023)
CREATE_MISSING_GOLDEN = os.getenv("CREATE_MISSING_GOLDEN", 'False').lower() in ('true', '1', 't')
RECREATE_BROKEN_GOLDEN = os.getenv("RECREATE_BROKEN_GOLDEN", 'False').lower() in ('true', '1', 't')


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


def diff_strings(a, b):
    output = []
    matcher = difflib.SequenceMatcher(None, a, b)
    green = '\x1b[38;5;16;48;5;2m'
    red = '\x1b[38;5;16;48;5;1m'
    endgreen = '\x1b[0m'
    endred = '\x1b[0m'

    for opcode, a0, a1, b0, b1 in matcher.get_opcodes():
        if opcode == 'equal':
            output.append(a[a0:a1])
        elif opcode == 'insert':
            output.append(f'{green}{b[b0:b1]}{endgreen}')
        elif opcode == 'delete':
            output.append(f'{red}{a[a0:a1]}{endred}')
        elif opcode == 'replace':
            output.append(f'{green}{b[b0:b1]}{endgreen}')
            output.append(f'{red}{a[a0:a1]}{endred}')
    return ''.join(output)


print("Running execute tests:")

for name in os.listdir("./execute"):
  print(f"Running test '{name}'...")
  def_path = os.path.join("./execute", name, "definition.kore")
  params_json_path = os.path.join("./execute", name, "params.json")
  state_json_path = os.path.join("./execute", name, "state.json")
  resp_golden_path = os.path.join("./execute", name, "response.golden")
  with open(params_json_path, 'r') as params_json:
    with open(state_json_path, 'r') as state_json:
      params = json.loads(params_json.read())
      state = json.loads(state_json.read())
      params["state"] = state

      with subprocess.Popen(f"kore-rpc {def_path} --module TEST --server-port {PORT}".split()) as process:
        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
          while True:
            try:
              s.connect((HOST, PORT))
              print("Connected to server...")
              break
            except:
              pass
          # print(rpc_request_id1("execute", params))
          # print("-------------")
          # print(execute(state, 1))
          s.sendall(rpc_request_id1("execute", params))
          # s.sendall(execute(state, 1))
          resp = recv_all(s)
          print(resp)
          process.kill()

          if os.path.exists(resp_golden_path):
            print("Checking against golden file...")
            with open(resp_golden_path, 'rb') as resp_golden_raw:
              golden_json = resp_golden_raw.read()
              if golden_json != resp:
                print(f"Test '{name}' failed...")
                print(diff_strings(str(golden_json), str(resp)))
                if RECREATE_BROKEN_GOLDEN:
                  with open(resp_golden_path, 'wb') as resp_golden_writer:
                    resp_golden_writer.write(resp)
                else:
                  exit(1)
              else:
                print(f"Test '{name}' passed...")
          elif CREATE_MISSING_GOLDEN or RECREATE_BROKEN_GOLDEN:
            with open(resp_golden_path, 'wb') as resp_golden_writer:
               resp_golden_writer.write(resp)
          else:
            print("Golden file not found...")
            exit(1)



