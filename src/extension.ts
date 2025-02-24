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
        const progs64DirPath = '/home/harsh/.opam/default/lib/coq/user-contrib/VST/progs64/proofgen.v';
        const filePath = path.dirname(document.uri.fsPath);
        const targetFilePath = path.join(filePath, "proofgen.v");

        fs.copyFile(progs64DirPath, targetFilePath, (err: any) => {
            if (err) {
                console.error(`Failed to copy file: ${err}`);
                vscode.window.showErrorMessage('Error copying file to progs64 directory.');
            } else {
                vscode.window.showInformationMessage(`${filePath} file copied`);
            }
        });

        // Process C files: Generate and save .v files
        if (document.languageId === "c") {
            generateAndSaveVFile(document.fileName);
        }
    });

    console.log('Congratulations, your extension "worcshop" is now active!');
}

function generateAndSaveVFile(cFilePath: string) {
    let parsedPath = path.parse(cFilePath);
    const newFilePath = path.join(parsedPath.dir, parsedPath.name + '.v');

   
    const clightgenCommand = `clightgen -normalize ${cFilePath} > "${newFilePath}"`;

    const { exec } = require("child_process");
    exec(clightgenCommand, (err: any, stdout: any, stderr: any) => {
        if (err) {
            console.error(`Error while executing clightgen: ${err}`);
            return;
        }
        if (stderr) {
            console.log(`clightgen stderr: ${stderr}`);
        } else {
            console.log(`${newFilePath} has been successfully generated.`);
        }
    });
}

export function deactivate() {}