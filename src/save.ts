// The module 'vscode' contains the VS Code extensibility API
// Import the module and reference it with the alias vscode in your code below
import { ChildProcessWithoutNullStreams, spawn } from 'child_process';
import * as readline from 'node:readline';
import { fetch } from 'undici';
import * as path from 'path';
import * as vscode from 'vscode';
import { ProofStatePanel } from "./panels/ProofStatePanel";
import { readFileSync } from 'fs';
const fs = require('fs');
var coq: ChildProcessWithoutNullStreams;
var reader: readline.Interface;
// this method is called when your extension is activated
// your extension is activated the very first time the command is executed
var targetFilePath:string;
var currDirPath:string;

export function activate(context: vscode.ExtensionContext) {
    
    vscode.workspace.onDidSaveTextDocument((document) => {
        const progs64DirPath = '/home/hrenik2/.opam/default/lib/coq/user-contrib/VST/progs64/proofgen.v';
        const filePath = path.dirname(document.uri.fsPath);
        targetFilePath = path.join(filePath, "proofgen.v");
        fs.copyFile(progs64DirPath, targetFilePath, (err: any) => {
            if (err) {
                console.error(`Failed to copy file: ${err}`);
                vscode.window.showErrorMessage('Error copying file to progs64 directory.');
            } else {
                vscode.window.showInformationMessage(`${filePath} file copied`);
            }
        });
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
        coq = spawn('/home/ghostxxx/anaconda3/bin/python3', [path.join(context.extensionPath, 'src', 'proofServer.py')]);
        coq.stderr.once('data', () => { runLine("Goal True.", f => runLine("Abort.", f => {})) ;});
        coq.stderr.on('data', e => { console.log(`Coq error: ${e}`); });
        coq.addListener('close', e => { console.log('Coq closed'); });
        coq.addListener('disconnect', () => { console.log('Coq disconnected'); });
        coq.addListener('exit', code => { console.log(`Coq exited with code ${code}`); });
    }

    function runFile(filePath: string){
        let parsedPath = path.parse(filePath);
        currDirPath = parsedPath.dir;
        const newfilePath= path.join(parsedPath.dir, parsedPath.name + '.v');
        const verifFilePath= path.join(parsedPath.dir, 'verif_' + parsedPath.name + '.v');
        const { exec } = require("child_process");
        // Define constant for reusable paths and flags
        const baseFlags = [
            `-Q ${parsedPath.dir} "" `,
            `-Q /mnt/c/Users/UIC/downloads/worcshop-main/worcshop-main TOP`,
            `-Q /home/hrenik2/.opam/default/lib/coq/user-contrib/VST/msl VST.msl`,
            `-Q /home/hrenik2/.opam/default/lib/coq/user-contrib/VST/sepcomp VST.sepcomp`,
            `-Q /home/hrenik2/.opam/default/lib/coq/user-contrib/VST/veric VST.veric`,
            `-Q /home/hrenik2/.opam/default/lib/coq/user-contrib/VST/floyd VST.floyd`,
            `-R /home/hrenik2/.opam/default/lib/coq/user-contrib/compcert compcert`,
            `-Q /home/hrenik2/.opam/default/lib/coq/user-contrib/VST/zlist VST.zlist`
        ];
        // Join the flags into a single string
        const flags = baseFlags.join(' ');
        const command = `clightgen -normalize ${filePath} &&
                        coqc ${flags} ${newfilePath} &&
                        coqc ${flags} ${targetFilePath} > ${verifFilePath}`;
        exec(command, (err: any, stdout: any, stderr: any) => {
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
            // Extract proof code from verif_*.v file, keeping only content within double quotes
            const words = readFileSync(verifFilePath, 'utf-8');
            const extractedCode = words.match(/"([^"]+)"/);
            // Check if 'extractedCode' is not null and 'extractedCode[1]' exists
            if (extractedCode && extractedCode[1]) {  
                const verifProof = extractedCode[1];
                runLine(verifProof, displayGoals);
            } else {
                console.error("Error: Unable to extract proof code from verif_*.v file. Matching double quotes not found.");
            }
            }
        });
    }

    // run a line of Coq through SerAPI via Alectryon
    function runLine(line: string, k: (frags: string) => void): void {
        console.log(`fetching http://127.0.0.1:5000/proof?` + new URLSearchParams({line: line, path: currDirPath}));
        fetch(`http://127.0.0.1:5000/proof?` + new URLSearchParams({line: line, path: currDirPath}))
        .then(response => { return response.json(); }, reason => console.error(`fetch failed: ${reason}`))
        .then(myJson => {
            var r = new Result();
            Object.assign(r, myJson);
            console.log();
            console.log(`Alectryon goal returned: ${r.goalConclusion}`);
            console.log();
            console.log(`Alectryon message returned: ${r.messageInfo}`);
            k(r.messageInfo);
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

// Result class definition to capture output from Alectryon
class Result{
    public goalConclusion = "";
    public messageInfo = "";
}