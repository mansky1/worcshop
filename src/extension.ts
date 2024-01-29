// The module 'vscode' contains the VS Code extensibility API
// Import the module and reference it with the alias vscode in your code below
import { ChildProcessWithoutNullStreams, spawn } from 'child_process';
import * as readline from 'node:readline';
import { fetch } from 'undici';
import * as path from 'path';
import * as vscode from 'vscode';
import { ProofStatePanel } from "./panels/ProofStatePanel";
import { readFileSync } from 'fs';

var coq: ChildProcessWithoutNullStreams;
var reader: readline.Interface;

// this method is called when your extension is activated
// your extension is activated the very first time the command is executed
export function activate(context: vscode.ExtensionContext) {
	console.log("test0");
	vscode.workspace.onDidSaveTextDocument((document) => {
		console.log("test1");
        if (document.languageId === "c") {
            runFile(document.fileName);
        }
    });
	
	// Use the console to output diagnostic information (console.log) and errors (console.error)
	// This line of code will only be executed once when your extension is activated
	console.log('Congratulations, your extension "worcshop" is now active!');

	// The command has been defined in the package.json file
	// Now provide the implementation of the command with registerCommand
	// The commandId parameter must match the command field in package.json
	let disposable = vscode.commands.registerCommand('worcshop.startCoq', startCoq);

	context.subscriptions.push(disposable);

	vscode.workspace.onDidChangeTextDocument(runNextLine);

	function startCoq(): void {
		console.log('Starting Coq...');
		coq = spawn('/home/ghostxxx/anaconda3/bin/python', [path.join(context.extensionPath, 'src', 'proofServer.py')]);
		coq.stderr.once('data', () => { runLine("Goal True.", f => runLine("Abort.", f => {})) ;});
		coq.stderr.on('data', e => { console.log(`Coq error: ${e}`); });
		coq.addListener('close', e => { console.log('Coq closed'); });
		coq.addListener('disconnect', () => { console.log('Coq disconnected'); });
		coq.addListener('exit', code => { console.log(`Coq exited with code ${code}`); });
	}

	function runFile(filePath: string){
		let parsedPath = path.parse(filePath);    
		const newfilePath= path.join(parsedPath.dir, parsedPath.name + '.v');
		console.log(newfilePath);   /// debugging
		const fileName = path.basename(filePath);   // not required
        console.log(filePath);  // debugging
		const { exec } = require("child_process");
		exec(`clightgen ${filePath}`, (err: any, stdout: any, stderr: any) => {
			if (err) {
				console.error(err);
				return;
			}
			if (stderr) {
				console.log(`stderr: ${stderr}`);
				return;
			}
			else{
			console.log("test passed");  // debugging
			const words = readFileSync(newfilePath, 'utf-8');
			//console.log(words);   debugging
			runLine(words , displayGoals);
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
}

// this method is called when your extension is deactivated
export function deactivate() {}

class Result{
	public result = "";
}
