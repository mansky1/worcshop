// The module 'vscode' contains the VS Code extensibility API
// Import the module and reference it with the alias vscode in your code below
import { ChildProcessWithoutNullStreams, spawn } from 'child_process';
import * as readline from 'node:readline';
import * as vscode from 'vscode';

var coq: ChildProcessWithoutNullStreams;
var reader: readline.Interface;
var blocked: boolean = false;

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

	async function startCoq(): Promise<void> {
		console.log('Starting Coq...');
		coq = spawn('sertop');
		coq.stderr.on('data', e => { console.log(`Coq error: ${e}`); });
		coq.addListener('close', e => { console.log('Coq closed'); });
		coq.addListener('disconnect', () => { console.log('Coq disconnected'); });
		coq.addListener('exit', code => { console.log(`Coq exited with code ${code}`); });
		//consume initial Feedback messages
		coq.stdout.on('data', e => { console.log(`Coq said: ${e}`);
			if(e.toString().indexOf('contents Processed') > -1){
				coq.stdout.removeAllListeners();
				reader = readline.createInterface(coq.stdout, coq.stdin);
				startup();
			}
		});
	}
}

// this method is called when your extension is deactivated
export function deactivate() {}

function logLines(n: number, k: (a: string) => void): (answer: string) => void {
	return (e => { console.log(`Coq said: ${e}`); if(n > 1){ reader.once('line', logLines(n - 1, k)); } else { k(e); } });
}

function runLine(line: string, k: (goals: string) => void): void {
	console.log(`Running line ${line}`);
	reader.question(`(Add () "${line}")`, logLines(2, a => { reader.once('line', logLines(1, b => {
		let m = a.match( /Added [0-9]+/g );
		if(m === null){ console.log(`Error: no Added in ${a}`); }
		else{
			let sid = parseInt(m[0].split(" ")[1]);
			reader.question(`(Exec ${sid})`, logLines(5, a => {
				reader.question(`(Query () Goals)`, logLines(2, a => { reader.once('line', logLines(1, b => {
					let goals = a.substring(a.indexOf("ObjList") + 7, a.length - 2);
					console.log(`Goals: ${goals}`);
					k(goals);
				})); }));
			}));
		}})); }));
}

function displayGoals(goals: string): void {
	console.log(`Displaying goals: ${goals}`);
	// alectryon fragments.v.json -o fragments.v.snippets.html
	// alectryon --frontend coq.json --backend snippets-html fragments.json -o fragments.v.snippets.html
}

function startup(): void {
	runLine("Goal True.", g =>
	runLine("Abort.", g => {}));
}

function runNextLine(e: vscode.TextDocumentChangeEvent): void {
	let change = e.contentChanges.map(e => e.text).join("");
	//change.split('').forEach(c => console.log(c.charCodeAt(0)));
	if(change === '\n' || change === '\r\n'){
		let line = e.document.lineAt(e.document.lineCount - 2).text;
		console.log('sending %s', line);
		runLine(line, goals => { displayGoals(goals); });
	}
}
