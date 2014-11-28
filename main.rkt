#lang racket/base
(require racket/match
         racket/list
         racket/flonum
         racket/fixnum
         racket/math)

(define (flclamp m x M)
  (flmax m (flmin x M)))

(define (flmodulo x y)
  (if (fl< x y)
      x
      (flmodulo (fl- x y) y)))

(define ((linear m M) t)
  (fl+ (fl* (fl- 1.0 t) m)
       (fl* t M)))
(define ((const v) t)
  v)
(define ((step m M) t)
  (if (fl< t 1.0)
      m
      M))

(struct timeline ())
(struct tl-unit timeline (f))
(struct tl-superimpose timeline
        (combiner left right))
(struct tl-loop timeline
        (inner))
(struct tl-append timeline
        (left right))
(struct tl-reverse timeline
        (inner))
(struct tl-scale timeline
        (inner scale))
(struct tl-map timeline
        (inner fun))
(struct tl-delay timeline
        (inner delay))

(define (tl-superimpose* comb tls)
  (foldr (λ (left right) (tl-superimpose comb left right))
         (first tls) (rest tls)))
(define (tl-bind a b)
  (tl-superimpose (λ (av bv) (bv av)) a b))

(define (tl-eval tl t)
  (match tl
    [(tl-unit f)
     (f (flclamp 0.0 t 1.0))]
    [(tl-superimpose comb left right)
     (comb (tl-eval left t)
           (tl-eval right t))]
    [(tl-loop inner)
     (tl-eval inner
              (flmodulo t (tl-length inner)))]
    [(tl-append left right)
     (define left-len (tl-length left))
     (if (fl<= t left-len)
         (tl-eval left t)
         (tl-eval right (fl- t left-len)))]
    ;; xxx reverseing a loop show reverse the inside, but this just
    ;; makes it time infinity all the time.
    [(tl-reverse inner)
     (define inner-len (tl-length inner))
     (tl-eval inner (fl- inner-len t))]
    [(tl-scale inner scale)
     (tl-eval inner (fl/ t scale))]
    [(tl-delay inner delay)
     (tl-eval inner (fl- t delay))]
    [(tl-map inner fun)
     (fun (tl-eval inner t))]))

;; xxx perhaps i should cache this
(define (tl-length tl)
  (match tl
    [(tl-unit _)
     1.0]
    [(tl-superimpose comb left right)
     (max (tl-length left)
          (tl-length right))]
    [(tl-loop inner)
     +inf.0]
    [(tl-append left right)
     (fl+ (tl-length left) (tl-length right))]
    [(tl-reverse inner)
     (tl-length inner)]
    [(tl-scale inner scale)
     (fl* (tl-length inner) scale)]
    [(tl-delay inner delay)
     (fl+ (tl-length inner) delay)]
    [(tl-map inner fun)
     (tl-length inner)]))

;; xxx are floats the right representation of time? as time increases,
;; they will be less accurate and i quickly leave the optimal space of
;; [-1,1]. if i use bignums, then they'll increase in memory as time
;; goes on.
(struct tl-state (tl time))

;; xxx how to add new animations?
(define (tlst-tick st step)
  (match-define (tl-state tl t) st)
  ;; xxx how does this give events?
  (tl-state tl (fl+ step t)))
(define (tlst-read st)
  (match-define (tl-state tl t) st)
  (tl-eval tl t))
(define (tlst-reset st)
  (match-define (tl-state tl t) st)
  (tl-state tl 0.0))
(define (tlst-init tl)
  (tl-state tl 0.0))

(define (tl-there-and-back tl)
  (tl-append tl (tl-reverse tl)))

(module+ test
  (require lux
           lux/chaos/gui
           lux/chaos/gui/key
           lux/chaos/gui/val
           pict)

  (define W 1024)
  (define H 768)

  (define left-to-right
    (tl-unit (linear (* -0.125 W) (* +0.125 W))))
  (define spinning
    (tl-unit (linear 0.0 (fl* 2.0 pi))))

  (define BCX (* 1/2 W))
  (define BCY (* 1/2 H))
  (define BR (sqrt (+ (sqr (/ BCX 3)) (sqr (/ BCY 3)))))
  (define (spinning-balls delta-big-theta)
    ;; xxx do i want these as separate functions or things inside of
    ;; "timeline"
    (tl-map
     (tl-superimpose
      cons
      (tl-superimpose
       cons
       (tl-loop
        (tl-there-and-back
         (tl-scale (tl-unit (linear 10.0 100.0))
                   60.0)))
       (tl-loop
        (tl-scale (tl-append (tl-unit (step "black" "red"))
                             (tl-unit (step "red" "black")))
                  30.0)))
      (tl-superimpose
       cons
       (tl-loop
        (tl-there-and-back
         (tl-scale left-to-right 60.0)))
       (tl-loop (tl-scale spinning 360.0))))
     (match-lambda
      [(cons (cons radius c) (cons d theta))
       (λ (big-theta)
         (define C (make-polar BR (+ big-theta delta-big-theta)))
         (define CX (+ BCX (real-part C)))
         (define CY (+ BCY (imag-part C)))
         (define center-p
           (colorize (disk 5) "blue"))
         (define border-p
           (colorize (disk 30) c))
         (cons (vector (+ CX d) CY center-p)
               (for/list ([i (in-range 4)])
                 (define ith-theta (+ theta (/ (* i pi) 2)))
                 (define p (make-polar radius ith-theta))
                 (vector (+ (+ CX d) (real-part p))
                         (+ CY (imag-part p))
                         border-p))))])))

  (define combined
    (tl-bind
     (tl-loop (tl-scale spinning 360.0))
     (tl-superimpose*
      (λ (x-fls y-fls)
        (λ (a)
          (append (x-fls a) (y-fls a))))
      (for/list ([i (in-range 4)])
        (define i.0 (fx->fl i))
        (tl-delay (spinning-balls (fl/ (fl* i.0 pi) 2.0)) (fl* i.0 30.0))))))

  (define (pin-over* base l)
    (for/fold ([base base]) ([x*y*p (in-list l)])
      (match-define (vector x y p) x*y*p)
      (pin-over base x y p)))
  (define (pin-over*/lines base origin l)
    (define combined (pin-over* base l))
    (for/fold ([combined combined]) ([x*y*p (in-list l)])
      (match-define (vector _ _ p) x*y*p)
      (pin-line combined origin cc-find p cc-find)))

  (struct example (gv tl-st)
          #:methods gen:word
          [(define (word-event w e)
             (cond
              [(eq? e 'close)
               #f]
              [(key-event? e)
               (struct-copy example w
                            [tl-st (tlst-reset (example-tl-st w))])]
              [else
               w]))
           (define (word-tick w)
             (struct-copy example w
                          [tl-st (tlst-tick (example-tl-st w) 1.0)]))
           (define (word-output w)
             (match-define ps (tlst-read (example-tl-st w)))
             ((example-gv w) (pin-over* (blank W H) ps)))])

  (call-with-chaos
   (make-gui)
   (λ ()
     (fiat-lux (example (make-gui/val) (tlst-init combined))))))
