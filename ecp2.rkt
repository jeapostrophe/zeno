#lang racket/base
(require (for-syntax racket/base
                     racket/syntax
                     syntax/parse
                     syntax/name)
         racket/match
         racket/set
         racket/stxparam
         "object-pool.rkt")

(struct *component (id fields init alloc! free! ref set!)
        #:methods gen:custom-write
        [(define (write-proc v port mode)
           (when mode
             (write-string
              (format "<component:~a>" (*component-id v)) port)))])
(define (make-component id fields)
  (*component
   id fields
   (λ ()
     (gvector))
   (λ (com-data e)
     (define e-ref (gvector-alloc! com-data))
     e-ref)
   (λ (com-data e-ref)
     (gvector-free! com-data e-ref))
   ;; xxx don't use lists but specialize to number of arguments
   (λ (com-data e-ref)
     (vector->values
      (gvector-ref com-data e-ref)))
   (λ (com-data e-ref . vals)
     (gvector-set! com-data e-ref (list->vector vals)))))
(define-syntax (component stx)
  (syntax-parse stx
    [(_ (f:id ...)
        (~and type (~or #:fixnum #:flonum #:racket)))
     (with-syntax ([name (or (syntax-local-infer-name #'stx)
                             (gensym 'component))])
       (syntax/loc stx
         (make-component 'name '(f ...))))]))
(define-syntax (define-component stx)
  (syntax-parse stx
    [(_ c:id com-b:expr)
     (with-syntax
         ([c? (format-id #'c "~a?" #'c)]
          [c! (format-id #'c "~a!" #'c)]
          [c^ (format-id #'c "~a^" #'c)])
       (syntax/loc stx
         (begin (define com-b-i com-b)
                (define c (component-binding-ref com-b-i))
                (define c? (component-binding-has? com-b-i))
                (define c! (component-binding-set! com-b-i))
                (define c^ (component-binding-remove! com-b-i)))))]))

(define-syntax-parameter new!
  (λ (stx)
    (raise-syntax-error #f "use of new! outside a procedure or processor" stx)))
(define-syntax (processor stx)
  (syntax-parse stx
    [(_ #:components [[ci:id com:expr] ...]
        #:query [e:id q:expr]
        [body:expr ...+])
     (with-syntax ([name (or (syntax-local-infer-name #'stx)
                             (generate-temporary))]
                   [(com-b ...) (generate-temporaries #'(ci ...))])
       (syntax/loc stx
         (λ (sys)
           (define com-b (bind-component sys com))
           ...
           (values (compile-query sys [[ci com-b] ...] q)
                   (let ()
                     (define-component ci com-b)
                     ...
                     (define this-new! (bind-new! sys))
                     (syntax-parameterize
                         ([new! (make-rename-transformer #'this-new!)])
                       (define name
                         (λ (e)
                           body ...))
                       name))))))]))

(define-syntax (procedure stx)
  (syntax-parse stx
    [(_ #:components [[ci:id com:expr] ...]
        [body:expr ...+])
     (syntax/loc stx
       (λ (sys)
         (define-component ci (bind-component sys com))
         ...
         (define this-new! (bind-new! sys))
         (syntax-parameterize ([new! (make-rename-transformer #'this-new!)])
           body ...)))]))

;; xxx added? and removed?
(define-syntax-parameter changed?
  (λ (stx)
    (raise-syntax-error #f "use of changed? outside of query" stx)))
(define-syntax (define-query-component stx)
  (syntax-parse stx
    [(_ c:id com-b:expr)
     (with-syntax
         ([c (format-id #'c "~a" #'c)]
          [c? (format-id #'c "~a?" #'c)])
       (syntax/loc stx
         (begin (define c com-b)
                (define c? (component-binding-has? c)))))]))
(define-syntax (compile-query stx)
  (syntax-parse stx
    [(_ sys:id [[ci:id com-b:expr] ...] q:expr)
     (syntax/loc stx
       (let ()
         (define-query-component ci com-b)
         ...
         (define this-changed? (bind-changed? sys))
         (syntax-parameterize ([changed? (make-rename-transformer #'this-changed?)])
           (compile-query-body
            q))))]))
(define-syntax (compile-query-body stx)
  (syntax-parse stx
    [(_ i:id)
     (syntax/loc stx
       i)]
    [(_ ((~literal changed?) i:id))
     (syntax/loc stx
       (λ (e)
         (changed? e i)))]
    [(_ ((~literal not) sub))
     (syntax/loc stx
       (let ([sub-c (compile-query-body sub)])
         (λ (e)
           (not (sub-c e)))))]
    [(_ ((~literal and)))
     (syntax/loc stx
       (λ (e) #t))]
    [(_ ((~literal and) left . right))
     (syntax/loc stx
       (let ([left-c (compile-query-body left)]
             [right-c (compile-query-body (and . right))])
         (λ (e)
           (and (left-c e) (right-c e)))))]
    [(_ ((~literal or)))
     (syntax/loc stx
       (λ (e) #f))]
    [(_ ((~literal or) left . right))
     (syntax/loc stx
       (let ([left-c (compile-query-body left)]
             [right-c (compile-query-body (or . right))])
         (λ (e)
           (or (left-c e) (right-c e)))))]))

;; xxx change to gvector
(define (make-entities)
  (make-hasheq))
(define (entities-new! es [name 'entity])
  (define e (gensym name))
  (hash-set! es e (make-hasheq))
  e)
(define (entities-ref es e)
  (hash-ref es e
            (λ ()
              (error 'entities-ref
                     "Key ~v not found in ~e"
                     e es))))
;; xxx (entities-delete! es e)
(define (entities-component-alloc! es e com com-ref)
  (hash-set! (entities-ref es e)
             com
             ;; xxx don't use vector
             (vector (box #f) com-ref)))
(define (entities-component-has? es e com)
  (hash-has-key? (entities-ref es e) com))
(define (entities-component-*ref es e com)
  (define e-ht (entities-ref es e))
  (hash-ref e-ht com #f))
(define (entities-component-ref es e com)
  (match (entities-component-*ref es e com)
    [#f
     #f]
    [(vector changed?-box com-ref)
     com-ref]))
;; xxx change to com->set mapping
;; xxx this is inefficient
(define (entities-reset-changed! es)
  (for* ([e-data (in-hash-values es)]
         [cb*ref (in-hash-values e-data)])
    (set-box! (vector-ref cb*ref 0) #f)))
(define (entities-component-changed? es e com)
  (unbox (vector-ref (entities-component-*ref es e com) 0)))
(define (entities-component-changed! es e com)
  (set-box! (vector-ref (entities-component-*ref es e com) 0) #t))
(define (entities-component-remove! es e com)
  (hash-remove! (entities-ref es e) com))

(define (make-component-mapping coms)
  (for/hash ([com (in-list coms)])
    (values com ((*component-init com)))))
(define (component-mapping-ref com-map com)
  (hash-ref com-map com
            (λ ()
              (error 'component-mapping-ref
                     "Key ~v not found in ~e"
                     com com-map))))

(define (make-query-cache)
  (make-hasheq))
(define (query-cache-add! qc query)
  (hash-set! qc query (mutable-seteq)))
(define (query-cache-entities qc query)
  (set->list
   (hash-ref qc query
             (λ ()
               (error 'query-cache-entities
                      "Key ~v not found in ~e"
                      query qc)))))
(define (query-cache-entity-add! qc e com)
  ;; xxx use com effectively to ignore some qs
  (for ([(q es) (in-hash qc)])
    (unless (set-member? es e)
      (when (q e)
        (set-add! es e)))))
(define (query-cache-entity-remove! qc e com)
  ;; xxx use com effectively to ignore some qs
  (for ([(q es) (in-hash qc)])
    (when (set-member? es e)
      (unless (q e)
        (set-remove! es e)))))

(struct *system (es cm qc po-box))
(struct *process-data (query work))
(define (system #:components coms
                #:processor-order po)
  (define po-box (box #f))
  (define qc (make-query-cache))
  (define sys
    (*system (make-entities) (make-component-mapping coms)
             qc po-box))
  (set-box! po-box
            (for/list ([layer (in-list po)])
              (for/list ([p (in-list layer)])
                (define-values (query work) (p sys))
                (query-cache-add! qc query)
                (*process-data query work))))
  sys)
(define (bind-new! sys)
  (define es (*system-es sys))
  (λ ([name 'entity])
    (entities-new! es name)))
(define (bind-changed? sys)
  (define es (*system-es sys))
  (λ (e com-b)
    (define com (component-binding-com com-b))
    (entities-component-changed? es e com)))

(struct component-binding (com ref has? set! remove!))
;; xxx memoize this so there's only one for each
(define (bind-component sys com)
  (define es (*system-es sys))
  (define qc (*system-qc sys))
  (match-define (*component _ _ _ c:alloc c:free! c:ref c:set!) com)
  (define com-data (component-mapping-ref (*system-cm sys) com))
  (define (cb:ref e)
    (define e-ref (entities-component-ref es e com))
    (c:ref com-data e-ref))
  (define (cb:has? e)
    (entities-component-has? es e com))
  (define (cb:set! e . vals)
    (define e-ref
      (match (entities-component-ref es e com)
        [#f
         (define com-ref (c:alloc com-data e))
         (entities-component-alloc! es e com com-ref)
         com-ref]
        [e-ref
         e-ref]))
    (entities-component-changed! es e com)
    (query-cache-entity-add! qc e com)
    (apply c:set! com-data e-ref vals))
  (define (cb:remove! e)
    (define e-ref (entities-component-ref es e com))
    (c:free! com-data e-ref)
    (entities-component-remove! es e com)
    (query-cache-entity-remove! qc e com))
  (component-binding com cb:ref cb:has? cb:set! cb:remove!))

(define (system-iterate! sys)
  (for ([ps (in-list (unbox (*system-po-box sys)))])
    ;; xxx can do each level of this tree in parallel
    (for ([q*p (in-list ps)])
      (system-process sys q*p))))
(define (system-process sys cs*i)
  (match-define (*process-data query process-entity) cs*i)
  (for ([e (in-list (query-cache-entities (*system-qc sys) query))])
    (process-entity e)))

(module+ test
  (require racket/match
           racket/set
           racket/list
           racket/math
           racket/fixnum
           racket/flonum)

  (define (flsgn x)
    (if (fl< x 0.0)
        -1.0
        1.0))

  (define Position
    (component (cx cy) #:flonum))
  (define Velocity
    (component (dx dy) #:flonum))
  (define Shape
    (component (hw hh) #:flonum))
  (define Collideable
    (component (data) #:racket))
  (define InCollisionDB
    (component (mx Mx my My) #:fixnum))
  (define Collided
    (component (who-am-i other-guy sep-vec) #:racket))

  (define Moving
    (processor
     #:components [[p Position] [v Velocity]]
     #:query [e (and p? v?)]
     [(define-values (cx cy) (p e))
      (define-values (dx dy) (v e))
      (p! e (fl+ cx dx) (fl+ cy dy))]))

  (define (vec2 x y) (cons x y))
  (define (vec2-x v2) (car v2))
  (define (vec2-y v2) (cdr v2))
  (define (vec2-len v2)
    (flsqrt (fl+ (flexpt (vec2-x v2) 2.0)
                 (flexpt (vec2-y v2) 2.0))))
  (define (vec2-normalize v2)
    (define v2-len (vec2-len v2))
    (vec2 (fl/ (vec2-x v2) v2-len)
          (fl/ (vec2-y v2) v2-len)))
  (define (vec2- u v)
    (vec2 (fl- (vec2-x u) (vec2-x v))
          (fl- (vec2-y u) (vec2-y v))))
  (define (vec2* s v)
    (vec2 (fl* s (vec2-x v))
          (fl* s (vec2-y v))))

  (define (compute-sep-vec e cx cy hw hh
                           ep cxp cyp hwp hhp)
    (define x-axis (flabs (fl- cx cxp)))
    (define cw (fl+ hw hwp))
    (define y-axis (flabs (fl- cy cyp)))
    (define ch (fl+ hh hhp))
    (cond
     [(or (fl> x-axis cw)
          (fl> y-axis ch))
      (values #f #f)]
     [else
      (define ox (flabs (fl- x-axis cw)))
      (define oy (flabs (fl- y-axis ch)))
      (define diff
        (vec2- (vec2 cx cy)
               (vec2 cxp cyp)))
      (define dir
        (vec2-normalize diff))
      (define-values (e-ep ep-e)
        (cond
         [(fl> ox oy)
          (define dy (fl* (flsgn (vec2-y dir)) oy))
          (values (vec2 0.0 dy)
                  (vec2 0.0 (fl* -1.0 dy)))]
         [(fl> oy ox)
          (define dx (fl* (flsgn (vec2-x dir)) ox))
          (values (vec2 dx 0.0)
                  (vec2 (fl* -1.0 dx) 0.0))]
         [else
          (define dx (fl* (flsgn (vec2-x dir)) ox))
          (define dy (fl* (flsgn (vec2-y dir)) oy))
          (values (vec2 dx dy)
                  (vec2 (fl* -1.0 dx) (fl* -1.0 dy)))]))
      (values e-ep ep-e)]))

  (define (check-compute-sep-vec
           e cx1 cy1 hw hh
           ep cxp1 cyp1 hwp hhp)
    (define-values (e-ep1 ep-e1)
      (compute-sep-vec
       e cx1 cy1 hw hh
       ep cxp1 cyp1 hwp hhp))
    (cond
     [(and e-ep1 ep-e1)
      (define cx2 (fl+ cx1 (vec2-x e-ep1)))
      (define cy2 (fl+ cy1 (vec2-y e-ep1)))
      (define cxp2 (fl+ cxp1 (vec2-x ep-e1)))
      (define cyp2 (fl+ cyp1 (vec2-y ep-e1)))
      (define-values (e-ep2 ep-e2)
        (compute-sep-vec
         e cx2 cy2 hw hh
         ep cxp2 cyp2 hwp hhp))
      (unless (and (not e-ep2)
                   (not ep-e2))
        (error 'check-compute-sep-vec
               "round 1 ~v\nresults ~v\nround 2 ~v\nresults ~v"
               (vector e cx1 cy1 hw hh
                       ep cxp1 cyp1 hwp hhp)
               (vector e-ep1 ep-e1)
               (vector e cx2 cy2 hw hh
                       ep cxp2 cyp2 hwp hhp)
               (vector e-ep2 ep-e2)))]
     [else
      (error 'check-compute-sep-vec
             "expected collision but didn't find one\nround 1 ~v"
             (vector e cx1 cy1 hw hh
                     ep cxp1 cyp1 hwp hhp))]))

  (check-compute-sep-vec
   'ball-against-bottom1 23.312867092421016 600.3077754858892 3.75 3.75
   'bottom-wall 400.0 630.0 400.0 30.0)
  (check-compute-sep-vec
   'ball-against-right 802.8663208393258 408.56311016268256 3.75 3.75
   'right-wall 830.0 300.0 30.0 300.0)
  (check-compute-sep-vec
   'ball-against-left -1.909902576697318 539.9099025766973 3.75 3.75
   'left-wall -30.0 300.0 30.0 300.0)
  (check-compute-sep-vec
   'ball-against-bottom2 113.22363916083972 602.5293319383622 3.75 3.75
   'bottom-wall 400.0 630.0 400.0 30.0)
  (check-compute-sep-vec
   'bottom-wall 400.0 630.0 400.0 30.0
   'ball-against-bottom3 113.22363916083972 602.5293319383622 3.75 3.75)
  (check-compute-sep-vec
   'ball-against-left2 -0.20880579214336592 303.4569465849744 3.75 3.75
   'left-wall -30.0 300.0 400.0 30.0)
  (check-compute-sep-vec
   'ball56 146.45590745581785 600.1578031798822 3.75 3.75
   'bottom-wall 400.0 630.0 400.0 30.0)

  (define (Collision)
    ;; xxx change to multi-dim -> set
    (define db (make-hash))
    (define resolution 5)
    (define (range cx hw)
      (values (fxquotient (fl->fx (flfloor (fl- cx hw))) resolution)
              (fx+ 1 (fxquotient (fl->fx (flceiling (fl+ cx hw))) resolution))))
    (define (overlaps? cx hw cxp hwp)
      (fl<= (flabs (fl- cx cxp))
            (fl+ hw hwp)))

    (processor
     #:components [[p Position] [s Shape] [c Collideable]
                   [idb InCollisionDB] [i Collided]]
     #:query
     [e (and (and p? s? c?)
             (or (not idb?)
                 (changed? p)
                 (changed? s)
                 (changed? c)))]
     [(define-values (cx cy) (p e))
      (define-values (hw hh) (s e))
      (when (idb? e)
        (define-values (omx oMx omy oMy) (idb e))
        (for* ([cx (in-range omx oMx)]
               [cy (in-range omy oMy)])
          (hash-update! db (cons cx cy)
                        (λ (old)
                          (remq e old))
                        '())))
      (define-values (mx Mx) (range cx hw))
      (define-values (my My) (range cy hh))
      (idb! e mx Mx my My)

      (define collisions (mutable-set))
      (define (compute-collision! ep)
        (unless (set-member? collisions ep)
          (define-values (cxp cyp) (p ep))
          (define-values (hwp hhp) (s ep))
          (define-values (e-ep ep-e)
            (compute-sep-vec
             e cx cy hw hh
             ep cxp cyp hwp hhp))
          (when e-ep
            (set-add! collisions ep)
            (i! e 'left ep e-ep)
            (i! ep 'right e ep-e))))
      (define (compute-collisions! l)
        (for-each compute-collision! l))
      (for* ([cx (in-range mx Mx)]
             [cy (in-range my My)])
        (hash-update! db (cons cx cy)
                      (λ (old)
                        (compute-collisions! old)
                        (cons e old))
                      '()))]))

  (define Bouncing
    (processor
     #:components [[p Position] [v Velocity] [i Collided] [c Collideable]]
     #:query [e (and v? i?)]
     [(define-values (x y) (p e))
      (define-values (dx dy) (v e))
      (define-values (who-am-i other-guy sep-vec) (i e))
      (p! e
          (fl+ x (vec2-x sep-vec))
          (fl+ y (vec2-y sep-vec)))
      (v! e
          (fl* (if (fl= 0.0 (vec2-x sep-vec))
                   1.0
                   -1.0)
               dx)
          (fl* (if (fl= 0.0 (vec2-y sep-vec))
                   1.0
                   -1.0)
               dy))
      (i^ e)]))

  (define (Drawing vs)
    (processor
     #:components [[p Position] [s Shape] [v Velocity]]
     #:query [e (and p? s?)]
     [(define-values (cx cy) (p e))
      (define-values (hw hh) (s e))
      (set-box!
       vs
       (cons
        (vector (fl- cx hw)
                (fl- cy hh)
                (filled-rectangle (fl* 2.0 hw) (fl* 2.0 hh)))
        (unbox vs)))]))

  (define Testing
    (processor
     #:components [[p Position] [c Collideable]]
     #:query [e p?]
     [(define-values (cx cy) (p e))
      (define-values (d) (c e))
      (when (and (eq? 'ball d)
                 (or (fl< cx 0.0)
                     (fl< Width.0 cx)
                     (fl< cy 0.0)
                     (fl< Height.0 cy)))
        (error 'Testing "object ~v out of bounds at ~v,~v"
               e cx cy))]))

  (define (Game vs)
    (system
     #:components
     (list Position Velocity Shape Collideable InCollisionDB Collided)
     #:processor-order
     (list (list Moving)
           (list (Drawing vs) (Collision))
           (list Bouncing)
           ;;(list Testing)
           empty)))

  (define Width 800)
  (define Width.0 (fx->fl Width))
  (define Height 600)
  (define Height.0 (fx->fl Height))
  (define WallThickness 30.0)
  (define Init!
    (procedure
     #:components [[p Position] [s Shape] [v Velocity] [c Collideable]]
     [(define (wall! cx cy hw hh d)
        (define w (new! 'wall))
        (p! w cx cy)
        (s! w hw hh)
        (c! w d))
      (wall! (fl- 0.0 WallThickness) (fl/ Height.0 2.0)
             WallThickness (fl/ Height.0 2.0)
             'horizontal)
      (wall! (fl+ Width.0 WallThickness) (fl/ Height.0 2.0)
             WallThickness (fl/ Height.0 2.0)
             'horizontal)
      (wall! (fl/ Width.0 2.0) (fl- 0.0 WallThickness)
             (fl/ Width.0 2.0) WallThickness
             'vertical)
      (wall! (fl/ Width.0 2.0) (fl+ Height.0 WallThickness)
             (fl/ Width.0 2.0) WallThickness
             'vertical)

      (for ([i (in-range 50)])
        (define b (new! 'ball))
        (define hw (fl/ WallThickness 8.0))
        (define hh hw)
        (define dir
          (make-polar (fl/ WallThickness 4.0)
                      (fl* pi (fl/ (fx->fl (random 360)) 360.0))))
        (p! b
            (fx->fl (random Width))
            (fx->fl (random Height)))
        (c! b 'ball)
        (v! b (real-part dir) (imag-part dir))
        (s! b hw hh))]))

  (require lux
           lux/chaos/gui
           lux/chaos/gui/key
           lux/chaos/gui/val
           pict)

  (struct example (gv vs sys)
          #:methods gen:word
          [(define (word-fps w)
             30.0)
           (define (word-event w e)
             (cond
              [(eq? e 'close)
               #f]
              [else
               w]))
           (define (word-tick w)
             (set-box! (example-vs w) '())
             (system-iterate! (example-sys w))
             w)
           (define (word-output w)
             (define vs (unbox (example-vs w)))
             (define p
               (for/fold ([base (blank Width Height)])
                         ([x*y*p (in-list vs)])
                 (match-define (vector x y p) x*y*p)
                 (pin-over base x y p)))
             ((example-gv w) p))])

  (call-with-chaos
   (make-gui)
   (λ ()
     (define vs (box '()))
     (define sys (Game vs))
     (Init! sys)
     (fiat-lux (example (make-gui/val) vs sys)))))
