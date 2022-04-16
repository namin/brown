;; Reification: Reflection without Metaphysics
;; Daniel P. Friedman and Mitchell Wand
;; 1984


;; tagging functions and aliases

(define tagit cons)
(define tag car)

(define body cdr)
(define value-of car)
(define first car)
(define second cadr)
(define rest cdr)

(define wrap/quote (lambda (v) (list 'quote v)))

(define I (lambda (x) x))

;; syntactic auxiliaries

(define abs?
  (lambda (f) (eq? (tag f) 'abs)))
(define reifier?
  (lambda (f) (eq? (tag f) 'reify)))
(define simple?
  (lambda (f) (eq (tag f) 'simple)))

(define syntactic-type
  (lambda (e)
    (cond
      ((atom? e) 'identifier)
      ((abs? e) 'abstraction)
      (else 'application))))

;; the interpreter (Sections 2-3)

(define denotation
  (lambda (e)
    (case (syntactic-type e)
      (identifier (<identifier> e))
      (abstraction
       (let ((b (body e)))
         (<abs>
          (if (reifier? b)
              <reify>
              <simple>)
          (body b))))
      (application (<app> e)))))

(define <identifier>
  (lambda (e)
    (lambda (r k)
      (r e
         (lambda (cell)
           (k (value-of cell)))))))

(define <app>
  (lambda (e)
    (lambda (r k)
      ((denotation (first e))
       r
       (lambda (f)
         (f (rest e) r k))))))

(define <abs>
  (lambda (abs-builder e)
    (lambda (r k)
      (k (abs-builder
          (lambda (v* c)
            ((denotation (second e))
             (ext r (first e) v*)
             c)))))))

(define <reify>
  (lambda (fun)
    (lambda (e r k)
      (fun
       (list
        e
        (schemeU-to-brown r)
        (schemeK-to-brown k))
       wrong))))

(define <simple>
  (lambda (fun)
    (lambda (e r k)
      ((rec loop
            (lambda (e k)
              (if (null? e) (k '())
                  ((denotation (first e))
                   r
                   (lambda (v)
                     (loop
                      (rest e)
                      (lambda (w)
                        (k (cons v w)))))))))
       e ;; NOTE(namin): added e!
       (lambda (v*) (fun v* k))))))

(define schemeF-to-brown <simple>)

(define brown-to-schemeF
  (lambda (bf)
    (lambda (v* c)
      (bf (map wrap/quote v*) initenv c))))


(define schemeK-to-brown
  (lambda (k)
    (lambda (e r k1)
      (if (= (length e) 1)
          ((denotation (first e)) r k)
          (wrong
           (list
            "schemeK-to-brown: "
            "wrong number of args "
            e))))))

(define brown-to-schemeK
  (lambda (bf)
    (lambda (v)
      (bf (list (wrap/quote v)) initenv I))))

(define schemeU-to-brown
  (lambda (r)
    (lambda (e r1 k1)
      (if (= (length e) 1)
          ((denotation (first e))
           r1
           (lambda (v) (r v k1)))
          (wrong
           (list
            "schemeU-to-brown: "
            "wrong no of args "
            e))))))

(define brown-to-schemeU
  (lambda (bf)
    (lambda (v c)
      (bf (list (wrap/quote v)) initenv c)))) ;; note(namin): added list!

(define nullenv
  (lambda (v c)
    (wrong (list "brown: unbound id " v))))

(define ext
  (lambda (r vars vals)
    (if (= (length vars) (length vals))
        (lambda (v c)
          ((rec lookup
                (lambda (vars vals)
                  (cond ((null? vars) (r v c))
                        ((eq? (first vars) v)
                         (c vals))
                        (else (lookup
                               (rest vars)
                               (rest vals))))))
           vars vals))
        (begin
          (display
           "Brown: wrong number of actuals")
          (display (list "Formals: " vars))
          (display (list "Actuals: " vals))
          (wrong "ext failed")))))

;; auxiliaries for setting up initenv

;; convert direct scheme fcns to schemeF

(define scheme-to-schemeF
  (lambda (f)
    (lambda (v* c) (c (apply f v*)))))

(define initenv '())

(define define-brown1
  (lambda (name exp)
    (call/cc
     (lambda (caller)
       ((denotation exp)
        initenv
        (lambda (v)
          (set! initenv
            (ext initenv
                 (list name)
                 (list v)))
          (caller name)))))))

;; define-brown is a useful macro

(define-syntax define-brown
  (syntax-rules ()
    ((_ id val)
     (define-brown1 'id 'val))))

;; the top level (Section 4)

(define run
  (lambda (e)
    (call/cc
     (lambda (caller)
       ((denotation e) initenv caller)))))

(define wrong
  (lambda (v)
    (display (list "wrong: " v)) (reset)))

(define boot-initenv
  (lambda ()
    (let
        ((scheme-fn-table
          (list
           (cons 'car car)
           (cons 'cdr cdr)
           (cons 'cons cons)
           (cons 'eq? eq?)
           (cons 'atom? atom?)
           (cons 'null? null?)
           (cons 'add1 add1)
           (cons 'sub1 sub1)
           (cons '=0 (lambda (x) (= 0 x)))
           (cons '+ +)
           (cons '- -)
           (cons '* *)
           (cons 'print display)
           (cons 'length length)
           (cons 'read read)
           (cons 'ext
                 (lambda (br p* v*)
                   (schemeU-to-brown
                    (ext
                     (brown-to-schemeU br)
                     p*
                     v*))))
           (cons 'nullenv nullenv)
           (cons 'update-store
                 (lambda (x y)
                   (value-of (set-car! x y))))
           (cons 'reifier? reifier?)
           (cons 'simple? simple?)
           (cons 'abs? abs?)
           (cons 'wrong wrong)
           (cons 'ef
                 (lambda (bool x y) (if bool x y)))
           (cons 'newline newline)
           (cons 'meaning
                 (lambda (e r k)
                   ((denotation e)
                    (brown-to-schemeU r)
                    (brown-to-schemeK k)))))))
      (let ((initvars (map car scheme-fn-table))
            (initvals
             (map
              (lambda (x)
                (schemeF-to-brown
                 (scheme-to-schemeF (cdr x))))
              scheme-fn-table)))
        (set! initenv
          (ext (ext nullenv '(nil t) '(nil t))
               initvars
               initvals))
        (define-brown quote
          (abs reify (e r k) (k (car e))))))))

(boot-initenv)

;; defining special forms (Section 5)

(define-brown if
  (abs reify (e r k)
     (meaning (car e) r
              (abs simple (v)
                   (meaning
                       (ef v
                           (car (cdr e))
                           (car (cdr (cdr e))))
                     r
                     k)))))

(define-brown call/cc
  (abs simple (f)
       ((abs reify (e r k) (k (f k))))))

(define-brown macro
  (abs simple (bf)
       (abs reify (e r k)
            (meaning (bf e) r k))))

(define-brown lambda
  (macro
      (abs simple (e)
           (cons 'abs (cons 'simple e)))))

(define-brown set!
  (abs reify (e r k)
       (meaning (car (cdr e)) r
                (abs simple (v)
                     (k (update-store
                         (r (car e))
                         v))))))

(define-brown fix1
  (abs simple (f)
       ((abs simple (d) (d d))
        (abs simple (g)
             (abs simple (x) ((f (g g)) x))))))

(define-brown begin
  (abs reify (e r k)
       ((fix1
         (abs simple (loop)
              (abs simple (e)
                   (if (null? (cdr e))
                       (meaning (car e) r k)
                       (meaning (car e) r
                                (abs simple (v)
                                     (loop (cdr e))))))))
        e)))

#;
(define-brown lexpr
  (abs reify (e r k)
       (k (abs reify (e1 r1 k1)
               (meaning* e1 r1
                         (abs simple (v*)
                              (meaning
                                  (car (cdr e))
                                (ext r (car e) (cons v* nil))
                                k1)))))))

#;
(define-brown list (lexpr (v) v))

(define-brown attach
  (abs reify (e r k)
       (meaning
           (car (cdr e))
         (abs simple (v)
              (begin
                (if (eq? v (car e))
                    (print '"Probed!") ;; NOTE(namin): added '!
                    nil)
                (r v)))
         k)))

#|
(run '(if (=0 '0) '1 '2))
(run '(attach x ((abs simple (x) (+ x '1)) '2)))
(set! initenv (ext initenv (list 'x) (list 2)))
(run '(attach x (+ x '1)))
(run '(attach x (+ x x x '1)))
|#
