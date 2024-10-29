from flask import Flask, request
from alectryon.serapi import SerAPI
from alectryon.cli import *
from alectryon.core import RichSentence
from graphVisualizer import generate_proof_graph

# Global variables
app = Flask(__name__)
serapi_instance = None
args = [
    "-Q", "/home/hrenik2,",
    "-Q", "/mnt/c/Users/UIC/downloads/worcshop-main/worcshop-main,TOP",
    "-Q", "/home/hrenik2/.opam/default/lib/coq/user-contrib/VST/msl,VST.msl",
    "-Q", "/home/hrenik2/.opam/default/lib/coq/user-contrib/VST/sepcomp,VST.sepcomp",
    "-Q", "/home/hrenik2/.opam/default/lib/coq/user-contrib/VST/veric,VST.veric",
    "-Q", "/home/hrenik2/.opam/default/lib/coq/user-contrib/VST/floyd,VST.floyd",
    "-R", "/home/hrenik2/.opam/default/lib/coq/user-contrib/compcert,compcert",
    "-Q", "/home/hrenik2/.opam/default/lib/coq/user-contrib/VST/zlist,VST.zlist"
]

@app.route('/proof')
def proof():
    global serapi_instance
    path = request.args.get('path')
    if serapi_instance is None:
        serapi_instance = SerAPI(args=args, fpath=path, binpath=None)
        serapi_instance.reset()
    output = run_line(request.args.get('line'))
    return output

def run_line(line):
    goal_conclusion, message_info = None, None
    annotated = [serapi_instance.run(line)]
    transformed = list(apply_transforms(annotated, "coq"))

    for transformed_lst in transformed:
        for sentence in transformed_lst:
            # Check if sentence is an instance of RichSentence 
            if isinstance(sentence, RichSentence):
                    
                    # Check if sentence has goals
                    if sentence.outputs and sentence.outputs[1].goals:
                        # Extract first goal -  # Assuming we want first goal
                        goal = sentence.outputs[1].goals[0] 
                        # Get conclusion content
                        goal_conclusion = goal.conclusion.contents

                    # Check if sentence has messages
                    if sentence.outputs and sentence.outputs[0].messages:
                        # Extract first message -  # Assuming we want first message
                        message = sentence.outputs[0].messages[0] 
                        # Get message contents
                        message_info = message.contents

    print(goal_conclusion) # debugging

    # Function call to generate and render a visual graph from goal conclusion contents
    if goal_conclusion:
        generate_proof_graph(goal_conclusion)
        
    return {
            "goalConclusion" : goal_conclusion, 
            "messageInfo" : message_info
           }

if __name__ == "__main__":
    app.run(host='0.0.0.0', port=5000)
