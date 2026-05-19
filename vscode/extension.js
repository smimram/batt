const fs = require('fs');
const path = require('path');
const cp = require('child_process');
const vscode = require('vscode');

class BattOutputViewProvider {
  constructor(context) {
    this.context = context;
    this.view = undefined;
    this.lastRendered = '';
    this.isRunning = false;
    this.refreshTimer = undefined;
  }

  resolveWebviewView(webviewView) {
    this.view = webviewView;
    webviewView.webview.options = {
      enableScripts: false,
      localResourceRoots: []
    };
    webviewView.webview.html = this.renderHtml(this.lastRendered || 'Open a .batt file to see its output.');
    this.refresh();

    webviewView.onDidDispose(() => {
      if (this.view === webviewView) {
        this.view = undefined;
      }
    });
  }

  async refresh() {
    const editor = vscode.window.activeTextEditor;
    const document = editor && editor.document;

    if (!document || document.languageId !== 'batt') {
      this.update('Open a .batt file to see its output.');
      return;
    }

    if (!document.fileName) {
      this.update('This document has no file on disk yet.');
      return;
    }

    const workspaceFolder = vscode.workspace.getWorkspaceFolder(document.uri);
    if (!workspaceFolder) {
      this.update('Open the workspace root that contains the BATT project.');
      return;
    }

    if (this.isRunning) {
      return;
    }

    this.isRunning = true;
    this.update(
      document.isDirty
        ? `Running batt on unsaved changes in ${path.basename(document.fileName)}...`
        : `Running batt on ${path.basename(document.fileName)}...`
    );
    try {
      const source = await this.materializeDocument(document, workspaceFolder.uri.fsPath);
      try {
        const result = await runBatt(workspaceFolder.uri.fsPath, source.filePath);
        const text = formatResult(document.fileName, result);
        this.update(text);
      } finally {
        try {
          await source.dispose();
        } catch (error) {
          void error;
        }
      }
    } catch (error) {
      const message = error && error.message ? error.message : String(error);
      this.update(`Failed to run batt.\n\n${message}`);
    } finally {
      this.isRunning = false;
    }
  }

  scheduleRefresh() {
    if (this.refreshTimer) {
      clearTimeout(this.refreshTimer);
    }
    this.refreshTimer = setTimeout(() => {
      this.refreshTimer = undefined;
      this.refresh();
    }, 300);
  }

  async materializeDocument(document, workspaceRoot) {
    if (!document.isDirty) {
      return {
        filePath: document.fileName,
        dispose: async () => {}
      };
    }

    const tempDir = document.uri.scheme === 'untitled' ? workspaceRoot : path.dirname(document.fileName);
    const tempName = `.batt-live-${process.pid}-${Date.now()}-${Math.random().toString(16).slice(2)}.batt`;
    const tempPath = path.join(tempDir, tempName);
    await fs.promises.writeFile(tempPath, document.getText(), 'utf8');

    return {
      filePath: tempPath,
      dispose: async () => {
        try {
          await fs.promises.unlink(tempPath);
        } catch (error) {
          if (!error || error.code !== 'ENOENT') {
            throw error;
          }
        }
      }
    };
  }

  update(text) {
    this.lastRendered = text;
    if (this.view) {
      this.view.webview.html = this.renderHtml(text);
    }
  }

  renderHtml(message) {
    const escaped = escapeHtml(message);
    return `<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <style>
    body {
      padding: 0.75rem 0.9rem;
      font-family: var(--vscode-font-family);
      color: var(--vscode-foreground);
      background: var(--vscode-editor-background);
      line-height: 1.5;
    }
    .header {
      display: flex;
      align-items: center;
      justify-content: space-between;
      margin-bottom: 0.75rem;
      gap: 0.75rem;
    }
    .title {
      font-size: 0.9rem;
      font-weight: 600;
    }
    .hint {
      font-size: 0.75rem;
      color: var(--vscode-descriptionForeground);
    }
    pre {
      white-space: pre-wrap;
      word-break: break-word;
      margin: 0;
      padding: 0.75rem;
      border-radius: 6px;
      background: var(--vscode-editor-inactiveSelectionBackground);
      overflow: auto;
      font-family: var(--vscode-editor-font-family);
      font-size: var(--vscode-editor-font-size);
    }
  </style>
</head>
<body>
  <div class="header">
    <div class="title">BATT Output</div>
    <div class="hint">Updates on save and editor change</div>
  </div>
  <pre>${escaped}</pre>
</body>
</html>`;
  }
}

function activate(context) {
  const provider = new BattOutputViewProvider(context);
  context.subscriptions.push(
    vscode.window.registerWebviewViewProvider('batt.output', provider),
    vscode.commands.registerCommand('batt.refresh', () => provider.refresh()),
    vscode.window.onDidChangeActiveTextEditor(() => provider.refresh()),
    vscode.workspace.onDidChangeTextDocument((event) => {
      const editor = vscode.window.activeTextEditor;
      if (!editor || editor.document.uri.toString() !== event.document.uri.toString()) {
        return;
      }
      if (event.document.languageId === 'batt') {
        provider.scheduleRefresh();
      }
    }),
    vscode.workspace.onDidSaveTextDocument((document) => {
      if (document.languageId === 'batt') {
        provider.refresh();
      }
    })
  );
}

function deactivate() {}

function formatResult(fileName, result) {
  const stdout = result.stdout.trim();
  const stderr = result.stderr.trim();
  if (result.code === 0) {
    return `batt succeeded for ${path.basename(fileName)}\n\n${stdout || '(no output)'}`;
  }
  const pieces = [
    `batt failed for ${path.basename(fileName)} (exit ${result.code})`,
    stdout ? `\nstdout:\n${stdout}` : '',
    stderr ? `\nstderr:\n${stderr}` : ''
  ];
  return pieces.join('');
}

function runBatt(workspaceRoot, fileName) {
  return new Promise((resolve, reject) => {
    const builtExe = path.join(workspaceRoot, '_build', 'default', 'src', 'batt.exe');
    const args = fs.existsSync(builtExe)
      ? [builtExe, '-I', 'stdlib', fileName]
      : ['exec', 'batt', fileName];
    const command = fs.existsSync(builtExe) ? builtExe : 'dune';
    const commandArgs = fs.existsSync(builtExe) ? ['-I', 'stdlib', fileName] : args;

    cp.execFile(command, commandArgs, { cwd: workspaceRoot, maxBuffer: 1024 * 1024 }, (error, stdout, stderr) => {
      if (error && typeof error.code !== 'number') {
        reject(error);
        return;
      }
      resolve({
        code: error && typeof error.code === 'number' ? error.code : 0,
        stdout: stdout || '',
        stderr: stderr || ''
      });
    });
  });
}

function escapeHtml(value) {
  return value
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;')
    .replace(/'/g, '&#39;');
}

module.exports = {
  activate,
  deactivate
};
