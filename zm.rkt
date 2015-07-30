#lang racket/base
(require racket/flonum
         racket/fixnum
         racket/match)

;; Zeno's Machine
;;
;; Write straight-line code where we assume that each code block has
;; many threads simultaneously running it, so we explicitly manage the
;; static data for that code block in a homogenous array then deal
;; with transitions. Furthermore, threads can start speculative tasks
;; with a deadline, called Prophecies.

;; TaggedBlockData = Nat x Data
;; Block = (CVector Data) x Nat x (Nat -> Bool)
;; Prophecy = Deadline x (Duration -> Void) x (Box Value) x (Box bool)
;; Machine = (Vectorof Block) x (PrioQueue Prophecy)

(struct block (data before! row! after!))
(define (block-init bi)
  (bi))
(define (block-run! m b)
  (match-define (block data before! row! after!) b)
  (before! m)
  (for ([i (in-list (hash-keys data))])
    (row! m i))
  (after! m))

(require data/heap)
(struct job (deadline work! done?-b answer-b))
(define (job<=? x y)
  (fl<= (job-deadline x) (job-deadline y)))
(define (job-run! pq left-over j)
  (match-define (job _ work! done? answer) j)
  (work! left-over)
  (unless (unbox done?)
    (prio-queue-add! pq j)))
(define (job-answer j)
  (match-define (job _ work! done? answer) j)
  (unless (unbox done?)
    (work! +inf.0))
  (unbox answer))

(define (make-prio-queue)
  (make-heap job<=?))
(define (prio-queue-add! pq j)
  (heap-add! pq j))
(define (prio-queue-empty? pq)
  (zero? (heap-count pq)))
(define (prio-queue-min pq)
  (begin0 (heap-min pq)
    (heap-remove-min! pq)))

(struct machine (block->i blocks pq))
(define (machine-run! freq block-inits)
  (define how-many-blocks (length block-inits))
  (define block->i (make-hasheq))
  (define blocks
    (for/vector #:length how-many-blocks
                ([bi (in-list block-inits)]
                 [i (in-naturals)])
      (define b (block-init bi))
      (hash-set! block->i b i)
      b))
  (define pq (make-prio-queue))
  (define m (machine block->i blocks pq))
  (let frame-loop ()
    (define start (current-inexact-milliseconds))
    (define next (fl+ start freq))
    (for ([b (in-vector blocks)])
      (block-run! m b))
    (define the-alarm-evt (alarm-evt next))
    (let left-over-loop ([try? #t])
      (if try?
          (sync/timeout
           (λ ()
             (cond
               [(prio-queue-empty? pq)
                (collect-garbage #t)
                #f]
               [else
                (define now (current-inexact-milliseconds))
                (define left-over (fl- next now))
                (define prof (prio-queue-min pq))
                (eprintf "SPEC\n")
                (job-run! pq left-over prof)
                #t]))
           the-alarm-evt)
          (sync the-alarm-evt)))
    (frame-loop)))

;;;

(module+ test
  (define freq (fl* 1000.0 (fl/ 1.0 60.0)))
  (machine-run! freq
                (list
                 (λ ()
                   (define data (make-hasheq))
                   (define (before! m) (void))
                   (define (after! m) (void))
                   (define (row! m i)
                     (match-define (and v (vector x y)) (hash-ref data i))
                     (eprintf "~a: ~a,~a\n" i x y)
                     (vector-set! v 0 (fxmodulo (fx+ 1 x) 31))
                     (vector-set! v 1 (fxmodulo (fx+ 1 y) 61)))
                   (printf "init\n")
                   (for ([i (in-range 10)])
                     (hash-set! data (gensym 'first) (vector i i)))
                   (block data before! row! after!)))))
