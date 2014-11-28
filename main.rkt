#lang racket/base
(require racket/match
         racket/flonum
         racket/fixnum
         racket/math)

(define (flmodulo x y)
  (if (fl< x y)
      x
      (flmodulo (fl- x y) y)))

(define (linear m M t)
  (fl+ (fl* (fl- 1.0 t) m)
       (fl* t M)))

(struct timeline ())
(struct tl-interval timeline
        (start tween end))
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

(define (tl-eval tl t)
  (match tl
    [(tl-interval start tween end)
     (tween start end t)]
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
    [(tl-reverse inner)
     (define inner-len (tl-length inner))
     (tl-eval inner (fl- inner-len t))]
    [(tl-scale inner scale)
     (tl-eval inner (fl/ t scale))]))

;; xxx perhaps i should cache this
(define (tl-length tl)
  (match tl
    [(tl-interval _ _ _)
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
     (fl* (tl-length inner) scale)]))

(struct tl-state (tl time))

;; xxx how to add new animations?
(define (tlst-tick st step)
  (match-define (tl-state tl t) st)
  ;; xxx how does this give events?
  (tl-state tl (fl+ step t)))
(define (tlst-read st)
  (match-define (tl-state tl t) st)
  (tl-eval tl t))
(define (tlst-init tl)
  (tl-state tl 0.0))

(module+ test
  (require lux
           lux/chaos/gui
           lux/chaos/gui/val
           pict)

  (define left-to-right
    (tl-interval -0.125 linear +0.125))

  (define spinning
    (tl-interval 0.0 linear (fl* 2.0 pi)))

  (define combined
    ;; xxx do i want these as separate functions or things inside of
    ;; "timeline"
    (tl-superimpose
     cons
     (tl-loop (tl-append (tl-scale left-to-right 60.0)
                         (tl-reverse (tl-scale left-to-right 60.0))))
     (tl-loop (tl-scale spinning 360.0))))

  (struct example (gv tl-st)
          #:methods gen:word
          [(define (word-event w e)
             (if (eq? e 'close)
                 #f
                 w))
           (define (word-tick w)
             (struct-copy example w
                          [tl-st (tlst-tick (example-tl-st w) 1.0)]))
           (define (word-output w)
             (match-define (cons d theta)
                           (tlst-read (example-tl-st w)))
             (define W 1024)
             (define H 768)
             (define p (make-polar 80 theta))
             (define (adjust x)
               (+ x d))
             ((example-gv w)
              (pin-over
               (pin-over
                (pin-over
                 (pin-over (blank W H)
                           (+ (* (adjust 3/4) W) (real-part p))
                           (+ (* 1/4 H) (imag-part p))
                           (disk 30))
                 (+ (* (adjust 1/4) W) (real-part p))
                 (+ (* 3/4 H) (imag-part p))
                 (disk 30))
                (+ (* (adjust 1/4) W) (real-part p))
                (+ (* 1/4 H) (imag-part p))
                (disk 30))
               (+ (* (adjust 3/4) W) (real-part p))
               (+ (* 3/4 H) (imag-part p))
               (disk 30))))])

  (call-with-chaos
   (make-gui)
   (λ ()
     (fiat-lux (example (make-gui/val) (tlst-init combined))))))
