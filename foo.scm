(define map
  (let ((null? null?)
	(car car) (cdr cdr)
	(cons cons) (apply apply))
  (letrec ((map-many
	    (lambda (f lists)
	      (if (null? (car lists))
		  '()
		  (cons
		   (apply f (map-one car lists))
		   (map-many f (map-one cdr lists))))))
	   (map-one
	    (lambda (f s)
	      (if (null? s)
		  '()
		  (cons (f (car s))
			(map-one f (cdr s)))))))
    (lambda (f . args)
      (map-many f args)))))

(map (lambda (x) (+ x 1)) '(1 2 3))

(define fold-left
  (lambda (fun init lst)
    (if (eq? lst '())
        init
        (fold-left fun (fun init (car lst)) (cdr lst)))))

(fold-left + 3 '(1 2))

(define fold-right
  (lambda (fun init lst)
    (if (eq? lst '())
        init
        (fun (car lst) (fold-right fun init (cdr lst))))))

(fold-right + 3 '(1 2))

(define cons*
 (lambda lst
   (fold-right cons '() lst)))

(cons* 1 2 3 4 5 6)