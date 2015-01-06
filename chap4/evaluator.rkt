;;;#lang r5rs

(define (filter p? xs)
  (cond ((null? xs) '())
        ((p? (car xs)) (cons (car xs) (filter p? (cdr xs))))
        (else (filter p? (cdr xs)))))

(define (error reason . args)
  (display "Error: ")
  (display reason)
  (for-each (lambda (arg) 
              (display " ")
              (write arg))
            args)
  (newline)
  (scheme-report-environment 5)) 

(define (self-evaluating? exp)
  (cond ((number? exp) #t)
        ((string? exp) #t)
        (else false)))

(define (variable? exp)
  (symbol? exp))

(define (tagged-list? exp tag)
  (if (pair? exp)
      (eq? (car exp) tag)
      #f))
 
(define (quoted? exp)
  (tagged-list? exp 'quote))

(define (extract-quotation-text exp)
  (cdr exp))

(define (assignement? exp)
  (tagged-list? exp 'set!))

(define (extract-assignement-variable exp)
  (cadr exp))

(define (extract-assignement-value exp)
  (caddr exp))

(define (make-lambda parameters body) 
        (cons 'lambda (cons parameters body)))

(define (definition? exp)
  (tagged-list? exp 'define))

(define (extract-variable-name exp)
  (if (symbol? (cadr exp))
      (cadr exp)
      (caadr exp)))

(define (extract-variable-value exp)
  (if (symbol? (cadr exp))
      (caddr exp)
      (make-lambda (cdadr exp)
                   (cddr exp))))

(define (lambda? exp)
  (tagged-list? exp 'lambda))

(define (extract-lambda-params exp)
  (cadr exp))

(define (extract-lambda-body exp)
  (cddr exp))

(define (self-evaluating? exp)
  (cond ((number? exp) #t)
        ((string? exp) #t)
        (else #f)))

(define (application? exp)
  (pair? exp))

(define (operator exp)
  (car exp))

(define (operands exp)
  (cdr exp))

(define (no-operands? exps)
  (null? exps))

(define (first-operand exps)
  (car exps))

(define (rest-operands exps)
  (cdr exps))

(define (list-of-values exps env)
  (if (no-operands? exps)
      '()
      (cons (eval-exp (first-operand exps) env)
            (list-of-values (rest-operands exps) env))))

(define (if? exp)
  (tagged-list? exp 'if))

(define (extract-predicate exp)
  (cadr exp))

(define (extract-if-consequent exp)
  (caddr exp))

(define (extract-if-alternative exp)
  (if (not (null? (cdddr exp)))
      (cdddr exp)
      ('false)))

(define (make-if predicate consequent alternate)
  (list 'if predicate consequent alternate))

(define (eval-if exp env)
  (if (true? (eval-exp (extract-predicate exp) env))
      (eval-exp (extract-if-consequent exp) env)
      (eval-exp (extract-if-alternative exp) env)))

(define (begin? exp)
  (tagged-list? exp 'begin))

(define (get-begin-actions exp)
  (cdr exp))

(define (last-exp? exps)
  (null? (cdr exps)))

(define (first-exp exps)
  (car exps))

(define (rest-exps exps)
  (cdr exps))

(define (sequence->exp seq)
  (cond ((null? seq) seq)
        ((last-exp? seq) (first-exp seq))
        (else (make-begin seq))))

(define (make-begin seq)
  (cons 'begin seq))

(define (cond? exp)
  (tagged-list? exp 'cond))

;;;(cond ((p) do) ((p2) do2) )
(define (cond-clauses exp) (cdr exp))

;;;((p) (do stuff))
(define (cond-predicate clause) 
  (car clause))

;;;((p) (do stuff))
(define (cond-actions clause)
  (cdr clause))

(define (cond-else-clause? clause)
  (equal? (con-predicate clause) 'else))

(define (cond->if exp)
  (expand-clauses (cond-clauses exp)))

(define (expand-clauses clauses)
  (cond ((null? clauses) 'false)
        ((cond-else-clause? (car clauses))
         (if (null? (cdr clauses))
             (sequence->exp (cond-actions (car clauses)))
             (error "*ELSE* clause must be last clause")))
        (else 
         (let ((clause (car clauses)))
           (make-if (cond-predicate clause)
                    (sequence-exp (cond-actions clause))
                    (expand-clauses (cdr clauses)))))))

(define (true? exp)
  (not (eq? exp #f)))

(define (false? exp)
  (not (eq? exp #f)))

(define (eval-sequence exps env)
  (cond ((last-exp? exps) (eval-exp (first-exp exps) env))
        (else (eval-exp (first-exp exps) env)
              (eval-sequence (rest-exps exps) env))))

(define (eval-assignement exp env)
  (set-variable-value! 
   (extract-assignement-variable exp)
   (eval-exp (extract-assignement-value exp) env)
   env)
  'ok)

(define (eval-definition exp env)
  (define-variable! 
    (extract-variable-name exp)
    (eval-exp (extract-variable-value exp) env)
    env)
  'ok)

(define (make-procedure args body env)
  (list 'procedure args (scan-out-defines body) env))

(define (compound-procedure? exp)
  (tagged-list? exp 'procedure))

(define (procedure-parameters p)
  (cadr p))

(define (procedure-body p)
  (caddr p))

(define (procedure-environment p)
  (cadddr p))

(define (enclosing-environment env) (cdr env))

(define (first-frame env) (car env))

(define empty-environment '())

;;; ((vars) val1 val2 ...)
(define (make-frame vars values)
  (cons vars values))

(define (frame-variables frame)
  (car frame))

(define (frame-values frame) 
  (cdr frame))

(define (add-binding-to-frame! var val frame)
  (set-car! frame (cons var (frame-variables frame)))
  (set-cdr! frame (cons val (frame-values frame))))

(define (extend-environment vars vals env)
  (cond ((eq? (length vars) (length vals))
         (cons (make-frame vars vals) env))
        ((< (length vars) (length vals))
         (error "*EXTEND ENV* not enough arguments applied"))
        (else 
         (error "*EXTEND ENV* too few arguments applied"))))

(define (lookup-variable v base-env)
  (define (look-up vars vals)
    (cond ((null? vars) '())
          ((and (eq? (car vars) v) (eq? '*unassigned* (list (car vals)))) 
           (error "*unassigned variable*: " v))
          ((eq? (car vars) v) (list (car vals)))
          (else (look-up (cdr vars) (cdr vals)))))
  (define (loop-env env)
    (if (eq? env empty-environment) 
        (error "Unbound variable" v)
        (let ((first (first-frame env)))
          (let ((result (look-up (frame-variables first) 
                                 (frame-values first))))
            (if (null? result)
                (loop-env (enclosing-environment env))
                (car result))))))
  (loop-env base-env))

(define (make-let params body)
  (cons 'let (list params body)))

(define (scan-out-defines body)
  (define (unassigned-vars defines) (map cadr defines))
  (define (make-unassigned v) (list v '*unassigned*))
  (define (extract-defines) (filter definition? body))
  (define (extract-not-defines) (filter (lambda (exp) (not (definition? exp))) body))
  (define (make-assignements defines)
    (map (lambda (define) (cons 'set! (cdr define))) defines))
  (let ((defines (extract-defines)) (rest-body (extract-not-defines)))
    (let ((vars (unassigned-vars defines)))
      (make-let (map make-unassigned vars)
                (append (make-assignements defines)
                        rest-body)))))

(define (set-variable-value! var val base-env)
  (define (set-frame-variable! vars vals)
    (cond ((null? vars) '())
          ((eq? (car vars) var) 
           (begin 
             (set-car! vals val)
             (list var)))
          (else (set-frame-variable! (cdr vars) (cdr vals)))))
  (define (set-env-variable! env)
    (if (eq? env empty-environment) 
        (error "Cannot bind into empty environment" var)       
        (let ((frame (first-frame env)))
          (let ((result (set-frame-variable! (frame-variables frame) (frame-values frame))))
            (if (null? result)
                (set-env-variable! (enclosing-environment env))
                (car result))))))
  (set-env-variable! base-env))

(define (define-variable! var val env)
  (let ((frame (first-frame env)))
    (define (add-var! vars vals)
      (cond ((null? vars) 
             (add-binding-to-frame! var val frame))
            ((eq? var (car vars)) 
             (set-car! vals val))
            (else (add-var! (cdr vars) (cdr vals)))))
    (add-var! (frame-variables frame) (frame-values frame))))

(define (make-application f args)
  (cons f args))

(define (let? exp)
  (tagged-list 'let exp))

;;; (let ((var1 exp1) (var2 exp2)) (body))
;;; ((lambda (var1 var2) (body)) (exp1 exp2))
(define (let->procedure exp)
  (define (assignements) (cadr exp))
  (define (extract-body) (cddr exp))
  (define (extract-vars) (map car (cadr exp)))
  (define (extract-args) (map cadr (cadr exp)))
  (define (extract-lambda)
    (make-lambda (extract-vars)
                 (extract-body)))
  (make-application (extract-lambda)
                    (extract-args)))


(define (primitive? exp)
  (tagged-list? exp 'primitive))

(define (primitive-implementation proc)
  (cadr proc))

(define (apply-primitive-proc proc args)
  (apply (primitive-implementation proc) args))


(define (letrec? exp)
  (tagged-list? exp 'letrec))

;;(letrec ((x a) (y b)) body)
;; (let ((x unsassigned) (y unassigned) (set! x a) (set))
(define (letrec->let exp)
  (define params (cadr exp))
  (define body (cddr exp))
  (define (make-unassigned-params)
    (map (lambda (p) (list (car p) '*unassigned*)) params))
  (define (make-assignements)
    (map (lambda (p) (cons 'set! p)) params))
  (define (make-body)
    (make-begin (append (make-assignements) body)))
  (make-let (make-unassigned-params)
            (make-body)))

(define (apply-proc procedure arguments)
  (cond ((primitive? procedure) 
         (apply-primitive-proc procedure arguments))
        ((compound-procedure? procedure)
         (eval-sequence 
          (procedure-body  procedure)
          (extend-environment
           (procedure-parameters procedure)
           arguments
           (procedure-environment procedure))))))

(define (analyze-self-evaluating exp)
  (lambda (env) exp))

(define (analyze-quoted exp)
  (let ((analyzed (extract-quotation-text exp)))
    (lambda (env) analyzed)))

(define (analyze-variable exp)
  (lambda (env) (lookup-variable exp env)))

;;(set! x <exp>)
(define (analyze-assignement exp)
  (let ((var (extract-assignement-variable exp))
        (pending-value (analyze (extract-assignement-value exp))))
    (lambda (env) 
      (set-variable-value! var (pending-value env) env))))

;;(define x <exp>)
;;(define (f x) (...))
(define (analyze-definition exp)
  (let ((var (extract-variable-name  exp))
        (pending-value (analyze (extract-variable-value exp))))
    (lambda (env) 
      (define-variable! var (pending-value env) env))))

(define (analyze-if exp)
  (let ((pred (extract-predicate exp))
        (conq (extract-if-consequent exp))
        (altr (extract-if-alternative exp)))
    (lambda (env)
      (if (pred env)
          (conq env)
          (altr env)))))
        
(define (analyze-lambda exp)
  (let ((params (extract-lambda-params exp))
        (body (extract-lambda-body exp)))
    (lambda (env) 
      (make-procedure params body env)))) 

(define (analyze-seq exps)
  (define (chain first-proc sec-proc)
    (lambda (env)
      (first-proc env) (sec-proc env)))
  (define (chain-calls next-proc rest-procs)
    (if (null? rest-procs)
        next-proc
        (chain-calls (chain next-proc (car rest-procs)) 
                     (cdr rest-procs))))
  (let ((procs (map analyze exps)))
    (if (null? procs)
        (error "empty sequence -- ANALYZE")
        (chain-calls (car procs) (cdr procs)))))


(define (run-procedure procedure arguments)
  (cond ((primitive? procedure) 
         (apply-primitive-proc procedure arguments))
        ((compound-procedure? procedure)
         ((extract-body procedure)
          (extend-environment
           (extract-parameters procedure)
           arguments
           (extract-environment procedure))))
        (else (error "Unknown procedure type" proc))))

(define (analyze-app exp)
  (let ((fproc (operator exp))
        (fargs (map analyze (operands exp))))
    (lambda (env)
      (run-procedure (fproc env)
                     (map (lambda (arg) (arg env)) fargs)))))

(define (analyze exp)
    (cond 
      ((self-evaluating? exp) (analyze-self-evaluating exp))
      ((variable? exp) (analyze-variable exp))
      ((quoted? exp) (analyze-quoted exp))
      ((assignement? exp) (analyze-assignement exp))
      ((definition? exp) (analyze-definition exp))
      ((if? exp) (analyze-if exp))
      ((let? exp) (analyze (let->procedure exp)))
      ((letrec? exp) (analyze (letrec->let exp)))
      ((lambda? exp) (analyze-lambda exp))
      ((begin? exp)
       (analyze-sequence (get-begin-actions exp)))
      ((cond? exp) (analyze (cond->if exp)))
      ((application? exp) (analyze-app exp))
      (else (error "Unknown expression -- EVAL" exp))))


(define (eval-exp exp env)
  ((analyze exp) env))

(define primitive-procedures
  (list (list 'car car)
        (list 'cdr cdr)
        (list 'cons cons)
        (list 'append append)
        (list '+ +)
        (list '* *)))

(define (primitive-procedure-names)
  (map car primitive-procedures))

(define (primitive-procedure-objects)
  (map (lambda (proc) (list 'primitive (cadr proc)))
       primitive-procedures))

(define (setup-environment)
  (let ((initial-env
         (extend-environment (primitive-procedure-names)
                             (primitive-procedure-objects)
                             empty-environment)))
    (define-variable! 'true #t initial-env)
    (define-variable! 'false #f initial-env)
    initial-env))


(define global-environment (setup-environment))

(define input-prompt ";;;M-Eval input:")
(define output-prompt ";;;M-Eval value:")

(define (prompt-for-input prompt)
  (newline) 
  (newline) 
  (newline) 
  (display prompt) 
  (newline))

(define (anounce-output prompt)
  (newline) 
  (display prompt) 
  (newline))

(define (user-print output)
  (if (compound-procedure? output)
      (display (list 'compound-procedure
                     (procedure-parameters output)
                     (procedure-body output)
                     '<procedure-env>))
      (display output)))

(define (driver-loop)
  (prompt-for-input input-prompt)
  (let ((input (read)))
    (let ((output (eval-exp input global-environment)))
      (anounce-output output-prompt)
      (user-print output)))
  (driver-loop))
