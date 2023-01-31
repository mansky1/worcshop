"use strict";
var __decorate = (this && this.__decorate) || function (decorators, target, key, desc) {
    var c = arguments.length, r = c < 3 ? target : desc === null ? desc = Object.getOwnPropertyDescriptor(target, key) : desc, d;
    if (typeof Reflect === "object" && typeof Reflect.decorate === "function") r = Reflect.decorate(decorators, target, key, desc);
    else for (var i = decorators.length - 1; i >= 0; i--) if (d = decorators[i]) r = (c < 3 ? d(r) : c > 3 ? d(target, key, r) : d(target, key)) || r;
    return c > 3 && r && Object.defineProperty(target, key, r), r;
};
Object.defineProperty(exports, "__esModule", { value: true });
exports.AppComponent = void 0;
const core_1 = require("@angular/core");
const webview_ui_toolkit_1 = require("@vscode/webview-ui-toolkit");
// In order to use the Webview UI Toolkit web components they
// must be registered with the browser (i.e. webview) using the
// syntax below.
(0, webview_ui_toolkit_1.provideVSCodeDesignSystem)().register((0, webview_ui_toolkit_1.vsCodeButton)());
// To register more toolkit components, simply import the component
// registration function and call it from within the register
// function, like so:
//
// provideVSCodeDesignSystem().register(
//   vsCodeButton(),
//   vsCodeCheckbox()
// );
let AppComponent = class AppComponent {
    constructor() {
        this.title = "proof-state";
        this.proofState = "Hello World!";
    }
    ngOnInit() {
        window.addEventListener('message', event => {
            switch (event.data.command) {
                case "updateProofState": {
                    this.proofState = event.data.proofState;
                }
            }
        });
    }
};
AppComponent = __decorate([
    (0, core_1.Component)({
        selector: "app-root",
        templateUrl: "./app.component.html",
        styleUrls: ["./app.component.css"],
    })
], AppComponent);
exports.AppComponent = AppComponent;
//# sourceMappingURL=app.component.js.map