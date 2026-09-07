;; batt-mode.el -- BATT major emacs mode

(defvar batt-font-lock-keywords
 '(
   ("--.*" . 'font-lock-comment-face)
   ("\\<\\(let\\|in\\|fun\\|λ\\|open\\|import\\)\\>\\|:\\|∷\\|=" . font-lock-keyword-face)
   ("\\<\\(true\\|false\\|tt\\|refl\\)\\>" . font-lock-constant-face)
   ("\\<\\(U\\|Type\\|TYPË\\|Bool\\|Unit\\|Empty\\)\\>\\|->\\|→\\|⨂\\|⊗\\|@\\|≡\\|⊥\\|♭\\|𝄫" . font-lock-builtin-face)
   ("\\<\\(\\)\\>" . font-lock-constant-face)
   ("^\\([^ (=]*\\)" 1 'font-lock-function-name-face)
  )
)

(defvar batt-mode-syntax-table
  (let ((st (make-syntax-table)))
    ;; Allow some extra characters in words
    (modify-syntax-entry ?_ "w" st)
    ;; Comments
    (modify-syntax-entry ?- ". 12" st)
    (modify-syntax-entry ?\n ">" st)
    st)
  "Syntax table for BATT major mode.")

(defvar batt-tab-width 4)

(defcustom batt-default-input-method "TeX"
  "Input method automatically activated in BATT buffers.
Set to nil to disable automatic activation."
  :type '(choice (const :tag "None" nil) string)
  :group 'batt)

(defcustom batt-command "batt"
  "Command used to type-check BATT files."
  :type 'string
  :group 'batt)

(defcustom batt-command-options '("--no-colors")
  "Options passed to `batt-command' before the file name."
  :type '(repeat string)
  :group 'batt)

(defconst batt-compilation-error-regexp-alist
  '((batt-single
     "in file \\([^ \n]+\\) line \\([0-9]+\\) characters? \\([0-9]+\\)" 1 2 3)
    (batt-multi
     "in file \\([^ \n]+\\) from line \\([0-9]+\\) character \\([0-9]+\\)" 1 2 3))
  "How to locate BATT error positions in the output buffer.")

(defconst batt-output-buffer-name "*batt*"
  "Name of the buffer holding the output of type-checking.")

(defun batt-check ()
  "Type-check the file of the current buffer with BATT.
On success, just report it in the echo area.  On failure, display
the output of the type-checker in a window at the bottom."
  (interactive)
  (unless buffer-file-name
    (error "Buffer is not visiting a file"))
  (when (buffer-modified-p) (save-buffer))
  (let ((buffer (get-buffer-create batt-output-buffer-name))
        (file buffer-file-name)
        (dir default-directory)
        status)
    (with-current-buffer buffer
      (setq buffer-read-only nil)
      (erase-buffer)
      (setq default-directory dir)
      (setq status (apply #'call-process batt-command nil t nil
                          (append batt-command-options (list file))))
      (goto-char (point-min))
      (compilation-mode)
      (setq-local compilation-error-regexp-alist batt-compilation-error-regexp-alist)
      (setq-local compilation-error-screen-columns nil))
    (if (eq status 0)
        (progn
          (when (get-buffer-window buffer) (quit-windows-on buffer))
          (message "BATT: %s type-checks." (file-name-nondirectory file)))
      (let ((window (display-buffer
                     buffer
                     '((display-buffer-reuse-window display-buffer-at-bottom)
                       (window-height . 0.3)))))
        (when window
          ;; scroll to the end of the output, where the error is
          (with-selected-window window
            (goto-char (point-max))
            (recenter -1))))
      (message "BATT: type-checking failed."))))

(defvar batt-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "C-c C-l") #'batt-check)
    map)
  "Keymap for BATT major mode.")

(define-derived-mode batt-mode fundamental-mode
  "BATT" "Major mode for BATT files."
  :syntax-table batt-mode-syntax-table
  (set (make-local-variable 'comment-start) "--")
  (set (make-local-variable 'comment-start-skip) "--+\\s-*")
  (set (make-local-variable 'font-lock-defaults) '(batt-font-lock-keywords))
  (setq mode-name "BATT")
  (when batt-default-input-method
    (set-input-method batt-default-input-method))
)

(provide 'batt-mode)

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.batt\\'" . batt-mode))
