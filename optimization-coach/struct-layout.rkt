#lang racket/base

;; Struct layout reports: suggest #:authentic for structs that nothing
;; outside the module can impersonate, and point out mutable fields
;; that are written with flonums (on Racket CS, each such write
;; allocates a box).
;;
;;   racket struct-layout.rkt file.rkt ...   prints the reports
;;
;; The check works on the fully expanded module. A struct is a candidate
;; when it has no parent, isn't prefab, isn't already authentic, and none
;; of its bindings is provided or used other than as the operator of a
;; direct call (a first-class use such as passing an accessor to
;; `struct/c` could lead to impersonation).

(require racket/list racket/path syntax/id-table "structs.rkt")

(provide report-struct-layout check-file)

;; A finding: kind is 'authentic or 'flonum-field
(struct finding (kind name msg stx uses))

(struct info (name authentic? ids struct-id ctor accessors mutators fields
               [direct-uses #:mutable] [escapes #:mutable]
               [flonum-writes #:mutable] srcloc stx))

(define fl-producers
  '(fl+ fl- fl* fl/ flabs flsqrt flexp fllog flsin flcos fltan flmin flmax
    flfloor flceiling flround fltruncate flexpt ->fl fx->fl exact->inexact
    real->double-flonum flvector-ref unsafe-fl+ unsafe-fl- unsafe-fl*
    unsafe-fl/ unsafe-flsqrt unsafe-flabs unsafe-flvector-ref))

(define (flonum-expr? e)
  (syntax-case* e (#%app quote) (lambda (a b) (eq? (syntax-e a) (syntax-e b)))
    [(quote v) (flonum? (syntax-e #'v))]
    [(#%app f . _) (and (identifier? #'f) (memq (syntax-e #'f) fl-producers) #t)]
    [_ #f]))

(define (check-file path)
  (define-values (dir _name _d?) (split-path (path->complete-path path)))
  (define stx
    (parameterize ([read-accept-reader #t] [read-accept-lang #t])
      (call-with-input-file path
        (lambda (in) (port-count-lines! in) (read-syntax (path->complete-path path) in)))))
  (define expanded
    (parameterize ([current-namespace (make-base-namespace)]
                   [current-load-relative-directory dir]
                   [current-directory dir])
      (expand stx)))
  (for ([f (in-list (analyze expanded path))])
    (printf "~a: ~a\n" (syntax-loc (finding-stx f)) (finding-msg f))))

(define (analyze expanded path)
  (define table (make-free-id-table)) ; id -> (cons info role)
  (define infos '())
  (define provided (make-free-id-table))

  ;; pass 1: struct definitions and provides
  (define (scan-defs body)
    (for ([form (in-list body)])
      (syntax-case* form (define-values #%provide module module* begin-for-syntax)
          (lambda (a b) (eq? (syntax-e a) (syntax-e b)))
        [(define-values (id ...) rhs)
         (let ([mst (find-make-struct-type #'rhs)])
           (when mst (register-struct! (syntax->list #'(id ...)) #'rhs mst form)))]
        [(#%provide spec ...)
         (for ([i (in-list (all-ids #'(spec ...)))]) (free-id-table-set! provided i #t))]
        [(module* _ #f (_mb . body)) (scan-defs (syntax->list #'body))]
        [_ (void)])))

  (define (register-struct! ids rhs mst form)
    (define args (syntax->list mst))
    ;; (#%app make-struct-type 'name parent init auto auto-v props insp proc imm guard ctor-name)
    (define a (cddr args))
    (define (arg i) (and (< i (length a)) (list-ref a i)))
    (define parent (arg 1))
    (define props (arg 5))
    (define insp (arg 6))
    (define nfields (syntax-e (arg 2)))
    (define (lit-false? e) (syntax-case e (quote) [(quote #f) #t] [_ (eq? (syntax-e e) #f)]))
    (define authentic? (mentions? props 'prop:authentic))
    (define prefab? (and insp (syntax-case insp (quote) [(quote prefab) #t] [_ #f])))
    (define name (syntax-case (arg 0) (quote) [(quote n) (syntax-e #'n)] [_ '?]))
    (cond
      [(or prefab? (not (lit-false? parent))) (void)]
      [else
       ;; ids are struct:, ctor, pred, then accessors / mutators in the
       ;; order `struct` produces them; classify by the rhs's
       ;; make-struct-field-accessor / -mutator calls
       (define acc-names (field-proc-names rhs 'make-struct-field-accessor))
       (define mut-names (field-proc-names rhs 'make-struct-field-mutator))
       (define rest-ids (cdddr ids))
       (define accessors (take rest-ids (min (length acc-names) (length rest-ids))))
       (define mutators (drop rest-ids (length accessors)))
       (define i (info name authentic? ids (car ids) (cadr ids) accessors mutators
                       acc-names 0 '() '() (syntax-loc form) form))
       (set! infos (cons i infos))
       (free-id-table-set! table (car ids) (cons i 'struct-type))
       (free-id-table-set! table (cadr ids) (cons i 'constructor))
       (free-id-table-set! table (caddr ids) (cons i 'predicate))
       (for ([a accessors]) (free-id-table-set! table a (cons i 'accessor)))
       (for ([m mutators] [n mut-names]) (free-id-table-set! table m (cons i (cons 'mutator n))))]))

  ;; pass 2: uses
  (define (walk e [operator? #f])
    (syntax-case* e (#%app quote quote-syntax lambda case-lambda #%plain-lambda
                     let-values letrec-values define-values define-syntaxes
                     begin-for-syntax #%provide #%require #%declare module module*
                     #%variable-reference set!)
        (lambda (a b) (eq? (syntax-e a) (syntax-e b)))
      [(quote . _) (void)]
      [(quote-syntax . _) (void)]
      [(#%provide . _) (void)]
      [(#%require . _) (void)]
      [(#%declare . _) (void)]
      [(define-syntaxes . _) (void)]
      [(begin-for-syntax . _) (void)]
      [(module . _) (void)]
      [(module* _ _ (_mb . body)) (for-each walk (syntax->list #'body))]
      [(define-values ids rhs) (walk #'rhs)]
      [(#%variable-reference . ids) (for ([i (syntax->list #'ids)]) (use! i #f #f))]
      [(set! id rhs) (use! #'id #f #f) (walk #'rhs)]
      [(#%app f arg ...)
       (identifier? #'f)
       (begin (use! #'f #t (syntax->list #'(arg ...)))
              (for-each walk (syntax->list #'(arg ...))))]
      [(form . rest)
       (and (identifier? #'form) (memq (syntax-e #'form) '(#%app if begin begin0 with-continuation-mark
                                                        #%expression #%plain-app)))
       (for-each walk (syntax->list #'rest))]
      [(lambda formals . body) (for-each walk (syntax->list #'body))]
      [(#%plain-lambda formals . body) (for-each walk (syntax->list #'body))]
      [(case-lambda [formals . body] ...) (for ([b (syntax->list #'(body ...))]) (for-each walk (syntax->list b)))]
      [(let-values ([ids rhs] ...) . body) (begin (for-each walk (syntax->list #'(rhs ...))) (for-each walk (syntax->list #'body)))]
      [(letrec-values ([ids rhs] ...) . body) (begin (for-each walk (syntax->list #'(rhs ...))) (for-each walk (syntax->list #'body)))]
      [id (identifier? #'id) (use! #'id #f #f)]
      [(a . b) (begin (walk #'a) (walk #'b))]
      [_ (void)]))

  (define (use! id direct? args)
    (define r (free-id-table-ref table id #f))
    (when r
      (define i (car r))
      (define role (cdr r))
      (cond
        [direct?
         (set-info-direct-uses! i (add1 (info-direct-uses i)))
         (when (and (pair? role) (eq? (car role) 'mutator) args (= 2 (length args))
                    (flonum-expr? (cadr args)))
           (set-info-flonum-writes! i (remove-duplicates (cons (cdr role) (info-flonum-writes i)))))]
        [else
         (set-info-escapes! i (cons (format "~a~a" (syntax-e id) (loc-suffix id)) (info-escapes i)))])))

  (syntax-case expanded ()
    [(_module _name _lang (_mb . body))
     (let ([body (syntax->list #'body)])
       (scan-defs body)
       (for ([form (in-list body)])
         (syntax-case* form (define-values) (lambda (a b) (eq? (syntax-e a) (syntax-e b)))
           [(define-values ids rhs)
            ;; the struct's own definition references its pieces; skip it
            (unless (for/or ([i (syntax->list #'ids)]) (free-id-table-ref table i #f))
              (walk #'rhs))]
           [_ (walk form)])))])

  (append*
   (for/list ([i (in-list (reverse infos))])
     (define exported (filter (lambda (id) (free-id-table-ref provided id #f)) (info-ids i)))
     (define escapes (remove-duplicates (info-escapes i)))
     (append
      (if (and (not (info-authentic? i)) (null? exported) (null? escapes))
          (list (finding 'authentic (info-name i)
                         (format "struct ~a: add #:authentic. Nothing outside this module can see its type, accessors or mutators, so no impersonator can reach it. Without #:authentic, every field access re-checks the instance because an impersonator could have intervened (~a direct uses)."
                                 (info-name i) (info-direct-uses i))
                         (info-stx i) (info-direct-uses i)))
          '())
      (if (pair? (info-flonum-writes i))
          (list (finding 'flonum-field (info-name i)
                         (format "struct ~a: mutable field~a ~a ~a written with flonums. Each write allocates a box; an immutable field holding an flvector stores the numbers unboxed."
                                 (info-name i)
                                 (if (pair? (cdr (info-flonum-writes i))) "s" "")
                                 (string-join* (map symbol->string* (reverse (info-flonum-writes i))))
                                 (if (pair? (cdr (info-flonum-writes i))) "are" "is"))
                         (info-stx i) (info-direct-uses i)))
          '())))))

;; Coach entry point: near-miss reports for the fully expanded module.
(define (report-struct-layout expanded)
  (for/list ([f (in-list (analyze expanded #f))])
    (define stx (finding-stx f))
    (define pos (syntax-position stx))
    (define span (syntax-span stx))
    (define start (and pos (sub1 pos)))
    (near-miss-report-entry
     (case (finding-kind f)
       [(authentic) "struct is not authentic"]
       [else "mutable flonum field"])
     (finding-msg f)
     stx
     'struct-layout
     start
     (and start span (+ start span))
     ;; badness grows with the number of direct uses
     (max 1 (min 20 (quotient (finding-uses f) 5)))
     '())))

;; ----------------------------------------

(define (find-make-struct-type rhs)
  (let loop ([e rhs])
    (syntax-case e ()
      [(app f . args)
       (and (identifier? #'app) (memq (syntax-e #'app) '(#%app #%plain-app))
            (identifier? #'f) (eq? (syntax-e #'f) 'make-struct-type))
       e]
      [(a . b) (or (loop #'a) (loop #'b))]
      [_ #f])))

(define (field-proc-names rhs which)
  (let loop ([e rhs])
    (syntax-case e (quote)
      [(app f _ _ (quote n))
       (and (identifier? #'f) (eq? (syntax-e #'f) which))
       (list (syntax-e #'n))]
      [(a . b) (append (loop #'a) (loop #'b))]
      [_ '()])))

(define (mentions? e sym)
  (and e
       (let loop ([e e])
         (syntax-case e ()
           [id (identifier? #'id) (eq? (syntax-e #'id) sym)]
           [(a . b) (or (loop #'a) (loop #'b))]
           [_ #f]))))

(define (all-ids e)
  (let loop ([e e])
    (syntax-case e ()
      [id (identifier? #'id) (list #'id)]
      [(a . b) (append (loop #'a) (loop #'b))]
      [_ '()])))

(define (syntax-loc s)
  (format "~a:~a:~a"
          (let ([src (syntax-source s)]) (if (path? src) (file-name-from-path src) src))
          (syntax-line s) (syntax-column s)))
(define (loc-suffix s) (if (syntax-line s) (format " (line ~a)" (syntax-line s)) ""))
(define (string-join* l) (apply string-append (add-between l ", ")))
(define (symbol->string* s) (if (symbol? s) (symbol->string s) (format "~a" s)))

(module+ main
  (require racket/cmdline)
  (command-line #:args files (for ([f (in-list files)]) (check-file f))))
