// The module 'vscode' contains the VS Code extensibility API
// Import the module and reference it with the alias vscode in your code below
import { ChildProcessWithoutNullStreams, spawn } from 'child_process';
import * as readline from 'node:readline';
import { fetch } from 'undici';
import * as path from 'path';
import * as vscode from 'vscode';
import { ProofStatePanel } from "./panels/ProofStatePanel";

var coq: ChildProcessWithoutNullStreams;
var reader: readline.Interface;

// this method is called when your extension is activated
// your extension is activated the very first time the command is executed
export function activate(context: vscode.ExtensionContext) {
	
	// Use the console to output diagnostic information (console.log) and errors (console.error)
	// This line of code will only be executed once when your extension is activated
	console.log('Congratulations, your extension "worcshop" is now active!');

	// The command has been defined in the package.json file
	// Now provide the implementation of the command with registerCommand
	// The commandId parameter must match the command field in package.json
	let disposable = vscode.commands.registerCommand('worcshop.startCoq', startCoq);

	context.subscriptions.push(disposable);

	vscode.workspace.onDidChangeTextDocument(runNextLine);
	/*vscode.workspace.onDidSaveTextDocument((document) => {
		console.log("test1");
        if (document.languageId === "c") {
            runFile(document.fileName);
        }
    });*/

	function startCoq(): void {
		console.log('Starting Coq...');
		coq = spawn('python3', [path.join(context.extensionPath, 'src', 'proofServer.py')]);
		coq.stderr.once('data', () => { runLine("Goal True.", f => runLine("Abort.", f => {})) });
		coq.stderr.on('data', e => { console.log(`Coq error: ${e}`); });
		coq.addListener('close', e => { console.log('Coq closed'); });
		coq.addListener('disconnect', () => { console.log('Coq disconnected'); });
		coq.addListener('exit', code => { console.log(`Coq exited with code ${code}`); });
	}

	function runFile(fileName: string){
		//const fileName = path.basename(filePath);
        console.log(fileName);
		const { exec } = require("child_process");
		exec(`clightgen ${fileName}`, (err: any, stdout: any, stderr: any) => {
			if (err) {
				console.error(err);
				return;
			}
			if (stderr) {
				console.log(`stderr: ${stderr}`);
				return;
			}
			else{
			console.log("test passed");
			}
		});
	}
	
	// run a line of Coq through SerAPI via Alectryon
	function runLine(line: string, k: (frags: string) => void): void {
		console.log(`fetching http://127.0.0.1:5000/proof?` + new URLSearchParams({line: line}));
		fetch(`http://127.0.0.1:5000/proof?` + new URLSearchParams({line: line}))
		.then(response => { return response.json(); }, reason => console.error(`fetch failed: ${reason}`))
		.then(myJson => {
			var r = new Result();
			Object.assign(r, myJson);
			console.log(`Alectryon returned: ${r.result}`);
			k(r.result);
    	}, reason => console.error(`couldn't get Alectryon output: ${reason}`));
	}

	function displayGoals(goals: string): void {
		ProofStatePanel.showGoals(context.extensionUri, goals);
	}

	// editor handler -- on newline, send the last line typed to Coq
	function runNextLine(e: vscode.TextDocumentChangeEvent): void {
		let change = e.contentChanges.map(e => e.text).join("");
		if(change === '\n' || change === '\r\n'){
			let line = e.document.lineAt(e.document.lineCount - 2).text;
			console.log('sending %s', line);
			runLine(line, displayGoals);
		}
	}

	// use SerAPI SaveDoc to save a compiled .vo file? Or should we be storing lines of Coq in another file before sending them?
	// for navigation, we can save the sentence ID associated with each line, and then use Cancel to retract
	// also check how VSCoq handles this?
}

// this method is called when your extension is deactivated
export function deactivate() {}

class Result{
	public result = "";
}
