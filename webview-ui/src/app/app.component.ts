import { Component, OnInit } from "@angular/core";
import { provideVSCodeDesignSystem, vsCodeButton } from "@vscode/webview-ui-toolkit";
import { vscode } from "./utilities/vscode";

// In order to use the Webview UI Toolkit web components they
// must be registered with the browser (i.e. webview) using the
// syntax below.
provideVSCodeDesignSystem().register(vsCodeButton());

// To register more toolkit components, simply import the component
// registration function and call it from within the register
// function, like so:
//
// provideVSCodeDesignSystem().register(
//   vsCodeButton(),
//   vsCodeCheckbox()
// );

@Component({
  selector: "app-root",
  templateUrl: "./app.component.html",
  styleUrls: ["./app.component.css"],
})
export class AppComponent implements OnInit{

  title = "proof-state";
  proofState: string = "<p>None</p>"
  
  ngOnInit(): void {

    window.addEventListener('message', event => {
        switch(event.data.command){
            case "updateProofState": {
                this.proofState = event.data.proofState;
            }
        }
        });
  }
}
