from flask import Flask, request
from alectryon.serapi import SerAPI
from alectryon.cli import *

app = Flask(__name__)

serapi_instance = None

@app.route('/proof')
def proof():
    global serapi_instance
    if serapi_instance is None:
        serapi_instance = SerAPI(args=(), fpath="-", binpath=None)
        serapi_instance.reset()
    return {"result": run_line(request.args.get('line')) }

def run_line(line):
    annotated = [serapi_instance.run(line)]
    transformed = apply_transforms(annotated, "coq")
    snippets = gen_html_snippets(transformed, "-", "coq", False, None)
    return dump_html_snippets(snippets)

if __name__ == "__main__":
    app.run(host='0.0.0.0', port=5000)
