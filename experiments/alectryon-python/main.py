from alectryon.serapi import SerAPI
from alectryon.cli import *
import json
import sys

serapi_instance = None

def run_line(line):
    global serapi_instance
    if serapi_instance is None:
        serapi_instance = SerAPI(args=(), fpath="-", binpath=None)
        serapi_instance.reset()

    print("---------------------------------------------------------")
    print("Running line:")
    print(line)
    print("---------------------------------------------------------")

    print("Annotated: ")
    annotated = [serapi_instance.run(line)]
    print(annotated)
    
    print("\nTransformed: ")
    transformed = apply_transforms(annotated, "coq")
    print(transformed)
    
    print("\nSnippets: ")
    snippets = gen_html_snippets(transformed, "-", "coq", False, None)
    print(snippets)

    print("\nHTML dump: ")
    html_dump = dump_html_snippets(snippets)
    print(html_dump)
    print("---------------------------------------------------------")

def main():
    argc = len(sys.argv)
    if not argc == 2:
        print("Usage: main.py filename.json")
        exit(-1)
    filename = sys.argv[1]
    f = open(filename)
    data = json.load(f)
    for stmt in data['statements']:
        run_line(stmt)
    


if __name__ == "__main__":
    main()
