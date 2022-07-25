import { getUri } from "../utilities/getUri";
import * as vscode from "vscode";

export class ProofStatePanel {
  public static currentPanel: ProofStatePanel | undefined;
  private readonly _panel: vscode.WebviewPanel;
  private _disposables: vscode.Disposable[] = [];

  private constructor(panel: vscode.WebviewPanel, extensionUri: vscode.Uri) {
    this._panel = panel;
    this._panel.onDidDispose(this.dispose, null, this._disposables);
    this._setWebviewMessageListener(this._panel.webview);
  }

  public static render(extensionUri: vscode.Uri) {
    if (ProofStatePanel.currentPanel) {
    } else {
      const panel = vscode.window.createWebviewPanel('proofState', 'Proof State', vscode.ViewColumn.Two,
        { enableScripts: true });
      ProofStatePanel.currentPanel = new ProofStatePanel(panel, extensionUri);
    }
  }

  public static showGoals(extensionUri: vscode.Uri, goals: string) {
    if (ProofStatePanel.currentPanel) {
        // ProofStatePanel.currentPanel._panel.reveal(vscode.ViewColumn.Two);
    } else {
      const panel = vscode.window.createWebviewPanel('proofState', 'Proof State', vscode.ViewColumn.Two,
        { enableScripts: true });

      ProofStatePanel.currentPanel = new ProofStatePanel(panel, extensionUri);
    }
    ProofStatePanel.currentPanel._panel.webview.html = ProofStatePanel.currentPanel._getWebviewContent(
      ProofStatePanel.currentPanel._panel.webview, extensionUri, goals);
  }

  public dispose() {
    ProofStatePanel.currentPanel = undefined;

    this._panel.dispose();

    while (this._disposables.length) {
      const disposable = this._disposables.pop();
      if (disposable) {
        disposable.dispose();
      }
    }
  }

  private _getWebviewContent(webview: vscode.Webview, extensionUri: vscode.Uri, goals: string): string {
    const toolkitUri = getUri(webview, extensionUri, [
      "node_modules",
      "@vscode",
      "webview-ui-toolkit",
      "dist",
      "toolkit.js", // A toolkit.min.js file is also available
    ]);

    return `<!DOCTYPE html>
    <html lang="en">
      <head>
        <meta charset="UTF-8">
        <meta name="viewport" content="width=device-width, initial-scale=1.0">
        <script type="module" src="${toolkitUri}"></script>
        <title>Proof State</title>
      </head>
      <body>
        ${goals}
      </body>
    </html>`;
  }

  private _setWebviewMessageListener(webview: vscode.Webview) {
    webview.onDidReceiveMessage(
      (message: any) => {
        const command = message.command;
        const text = message.text;

/*        switch (command) {
          case "hello":
            vscode.window.showInformationMessage(text);
            return;
        }*/
      },
      undefined,
      this._disposables
    );
  }
}
