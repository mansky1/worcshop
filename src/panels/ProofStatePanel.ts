import { getUri } from "../utilities/getUri";
import * as vscode from "vscode";
import { getNonce } from "../utilities/getNonce";

export class ProofStatePanel {
  public static currentPanel: ProofStatePanel | undefined;
  private readonly _panel: vscode.WebviewPanel;
  private _disposables: vscode.Disposable[] = [];

  private constructor(panel: vscode.WebviewPanel, extensionUri: vscode.Uri) {
    this._panel = panel;
    this._panel.onDidDispose(this.dispose, null, this._disposables);

    // Set the HTML content for the webview panel
    this._panel.webview.html = this._getWebviewContent(this._panel.webview, extensionUri);

    this._setWebviewMessageListener(this._panel.webview);
  }

  public static render(extensionUri: vscode.Uri) {
    if (ProofStatePanel.currentPanel) {
    } else {
      const panel = vscode.window.createWebviewPanel('proofState', 'Proof State', vscode.ViewColumn.Two,
        { enableScripts: true,
            localResourceRoots: [vscode.Uri.joinPath(extensionUri, "out"), vscode.Uri.joinPath(extensionUri, "webview-ui/build")],});
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

    this.currentPanel?._panel.webview.postMessage({
        command: "updateProofState",
        proofState: goals
    });
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

    /**
   * Defines and returns the HTML that should be rendered within the webview panel.
   *
   * @remarks This is also the place where references to the Angular webview build files
   * are created and inserted into the webview HTML.
   *
   * @param webview A reference to the extension webview
   * @param extensionUri The URI of the directory containing the extension
   * @returns A template string literal containing the HTML that should be
   * rendered within the webview panel
   */
    private _getWebviewContent(webview: vscode.Webview, extensionUri: vscode.Uri) {
        // The CSS file from the Angular build output
        const stylesUri = getUri(webview, extensionUri, ["webview-ui", "build", "styles.css"]);
        // The JS files from the Angular build output
        const runtimeUri = getUri(webview, extensionUri, ["webview-ui", "build", "runtime.js"]);
        const polyfillsUri = getUri(webview, extensionUri, ["webview-ui", "build", "polyfills.js"]);
        const scriptUri = getUri(webview, extensionUri, ["webview-ui", "build", "main.js"]);
    
        const nonce = getNonce();
    
        // Tip: Install the es6-string-html VS Code extension to enable code highlighting below
        return /*html*/ `
          <!DOCTYPE html>
          <html lang="en">
            <head>
              <meta charset="UTF-8" />
              <meta name="viewport" content="width=device-width, initial-scale=1.0" />
              <meta http-equiv="Content-Security-Policy" content="default-src 'none'; style-src ${webview.cspSource}; script-src 'nonce-${nonce}';">
              <link rel="stylesheet" type="text/css" href="${stylesUri}">
              <title>Hello World</title>
            </head>
            <body>
              <app-root></app-root>
              <script type="module" nonce="${nonce}" src="${runtimeUri}"></script>
              <script type="module" nonce="${nonce}" src="${polyfillsUri}"></script>
              <script type="module" nonce="${nonce}" src="${scriptUri}"></script>
            </body>
          </html>
        `;
      }

  private _setWebviewMessageListener(webview: vscode.Webview) {
    webview.onDidReceiveMessage(
      (message: any) => {
        const command = message.command;
        const text = message.text;
      },
      undefined,
      this._disposables
    );
  }
}
