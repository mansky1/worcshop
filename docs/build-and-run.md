The package.json file contains a set of defined scripts which can be used to install deps and build the extension along with the Angular application.

# Installing dependencis

Install package dependencies for both the extension and Angular webview source code.
```
npm run install:all
```

# Building

Build the Angular source code. This must always be done before compiling the extension.

For changes to the angular code to refelect in the application it must be built everytime before compileing the extension. This is because the Angular part is a self contained application and can be run independently of the vs-code extension. Thus, compiling only the extension would not reflect the changes made to the Angular application.

Command to build the Angular application:
```
npm run build:webview
```

# Compiling the VS Code extension

Compile the extension using:
```
npm run compile
```