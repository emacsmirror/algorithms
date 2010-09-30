;;; algorithms.el --- implementations of algorithms for CS381

;; Copyright (C) 2005 Michael Olson

;; This file is not part of GNU Emacs.

;; This is free software; you can redistribute it and/or modify it under
;; the terms of the GNU General Public License as published by the Free
;; Software Foundation; either version 2, or (at your option) any later
;; version.
;;
;; This is distributed in the hope that it will be useful, but WITHOUT
;; ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
;; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
;; for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
;; Boston, MA 02110-1301, USA.

;;; Commentary:

;; This is a listing of the algorithms that are implemented by this
;; file.  Helper functions are not listed here.  All algorithms have a
;; consistency check with sample data.

;; All Pairs (using Floyd-Warshall algorithm)
;; function: all-pairs
;; status: finished

;; Transitive Closure
;; function: transitive-closure
;; status: finished

;; Shortest path weights (using Dijkstra's Algorithm)
;; function: dijkstra
;; status: finished

;; Depth-First Search
;; function: dfs
;; status: finished

;; Stronly-Connected Components (using Kosaraju's Algorithm)
;; function: strongly-connected-components
;; status: not completely finished -- returns PREV from last DFS
;;         rather than connected components

;;; Code:

;;; Helper functions

(defun make-2dlist (rows cols fun)
  "Return a 2-dimensional list with ROWS 'rows' and COLS 'columns'.
FUN is a function that is called with current row and column.
The return value from FUN is used to intiailize the new
2-dimensional list."
  (let ((i 0)
        2dlist)
    (while (< i rows)
      (let ((j 0)
            row)
        (while (< j cols)
          (setq row (cons (funcall fun i j) row))
          (setq j (1+ j)))
        (setq 2dlist (cons (nreverse row) 2dlist)))
      (setq i (1+ i)))
    (nreverse 2dlist)))

(defun make-2dlist-from-2dlist (m fun)
  "Make a 2-dimensional list from M, another 2-dimensional list.
FUN is a function that is called with current row, column, and
value of M at that row and column."
  (make-2dlist (length m)
               (length (car m))
               `(lambda (row col)
                  (funcall ,fun row col
                           (nth col (nth row m))))))

(defun make-inf-weight-2dlist (weight-matrix)
  "Return a copy of WEIGHT-MATRIX, replacing any 0 entries with 'inf.
If current row and column are equal, use 0."
  (make-2dlist-from-2dlist
   weight-matrix
   #'(lambda (row col val)
       (if (eq row col)
           0
         (if (and val
                  (not (eq val 0)))
             val
           'inf)))))

(defun extract-min (q list)
  "Return the position of minimum element that is in both LIST and Q.
Anything in LIST that is not a number will not be considered."
  (let (min min-val)
    (dolist (el q)
      (let ((val (nth el list)))
        (when (and (numberp val)
                   (or (not min)
                       (< val min-val)))
          (setq min el
                min-val val))))
    (or min
        (car q))))

(defun adjacencies (n weight-matrix)
  "Return a list of vertices in WEIGHT-MATRIX that are adjacent to N."
  (let ((i 0)
        (row (nth n weight-matrix))
        adj)
    (while (< i (length row))
      (when (numberp (nth i row))
        (setq adj (cons i adj)))
      (setq i (1+ i)))
    adj))

(defun transpose-adjacencies (adjacencies &optional sort-fn)
  "Transpose the adjacency list in ADJACENCIES.
If SORT-FN is specified, use it to sort the list."
  (let ((new-adj (make-list (1+ (length adjacencies)) nil))
        (i 0))
    (dolist (row adjacencies)
      (setq i (1+ i))
      (dolist (el row)
        (let ((el-cdr (nthcdr el new-adj)))
          (setcar el-cdr (cons i (car el-cdr))))))
    (if sort-fn
        (mapcar #'(lambda (row)
                    (sort row sort-fn))
                (cdr new-adj))
      (cdr new-adj))))

(defun extract-forest (prev)
  "Return the connected components from the given PREV list."
  ;; NOTE: This doesn't work perfectly yet.
  (let* ((len (length prev))
         (processed (make-list len nil))
         (i 1)
         (adj-list-cur 0)
         adj-list)
    (while (<= i len)
      (let ((cur i)
            proc
            result)
        (while cur
          (cond ((setq proc (nth cur processed))
                 ;; add to previous proc'th adj-list
                 ;; but only if proc != adj-list-cur
                 (when (not (equal proc adj-list-cur))
                   (let ((row (nthcdr proc adj-list)))
                     (setcar row (nconc (car row) result))
                     (setq result nil)))
                 (setq cur nil))
                (t
                 (setcar (nthcdr cur processed) adj-list-cur)
                 (setq result (cons cur result)
                       cur (nth cur prev)))))
        (when result
          (setq adj-list (append adj-list (list result))
                adj-list-cur (1+ adj-list-cur))))
      (setq i (1+ i)))
    adj-list))

;;; All-Pairs algorithm

(defun all-pairs (graph)
  "Return the all-pairs representation of GRAPH.
This is based on the Floyd-Warshall algorithm.

A list will be returned.  The car is the distances.  The car of
the cdr is the predecessors.

It is assumed that GRAPH is sqaure."
  (let ((m (make-inf-weight-2dlist graph))
        (pred (make-2dlist-from-2dlist
               graph
               #'(lambda (row col val)
                   (if (> val 0)
                       row
                     'inf))))
        (len (length graph))
        (k 0))
    (while (< k len)
      (let ((i 0))
        (while (< i len)
          (let ((j 0))
            (while (< j len)
              (let* ((ik (nth k (nth i m)))
                     (kj (nth j (nth k m)))
                     (ij-elem (nthcdr j (nth i m)))
                     (sum (and (not (eq ik 'inf))
                               (not (eq kj 'inf))
                               (+ ik kj))))
                (when (and sum
                           (or (eq (car ij-elem) 'inf)
                               (> (car ij-elem) sum)))
                  (setcar ij-elem sum)
                  (setcar (nthcdr j (nth i pred))
                          (nth j (nth k pred)))))
              (setq j (1+ j))))
          (setq i (1+ i))))
      (setq k (1+ k)))
    (list m pred)))

;; Sample data
(unless (equal
         (all-pairs '((0 0 5 0 3)
                      (2 0 0 1 4)
                      (2 6 0 0 2)
                      (0 1 0 0 0)
                      (0 0 3 4 0)))
         '(((0 8 5 7 3)
            (2 0 7 1 4)
            (2 6 0 6 2)
            (3 1 8 0 5)
            (5 5 3 4 0))
           ((inf 3 0 4 0)
            (1 inf 0 1 1)
            (2 2 inf 4 2)
            (1 3 0 inf 1)
            (2 3 4 4 inf))))
  (message "all-pairs: Consistency error"))

;;; Transitive Closure algorithm

(defun transitive-closure (graph)
  "Return the transitive closure of GRAPH.

It is assumed that GRAPH is sqaure."
  (let ((m (make-2dlist-from-2dlist
            graph
            #'(lambda (row col val)
                (if (> val 0)
                    t
                  nil))))
        (len (length graph))
        (k 0))
    (while (< k len)
      (let ((i 0))
        (while (< i len)
          (let ((j 0))
            (while (< j len)
              (let ((ik (nth k (nth i m)))
                    (kj (nth j (nth k m))))
                (when (and ik kj)
                  (setcar (nthcdr j (nth i m))
                          t)))
              (setq j (1+ j))))
          (setq i (1+ i))))
      (setq k (1+ k)))
    m))

;; Sample data
(unless (equal
         (transitive-closure
          '((0 0 0 0 1)
            (1 0 0 0 0)
            (0 1 0 0 0)
            (0 0 0 1 0)
            (0 0 0 0 1)))
         '((nil nil nil nil t)
           (t nil nil nil t)
           (t t nil nil t)
           (nil nil nil t nil)
           (nil nil nil nil t)))
  (message "transitive-closure: Consistency error"))

;;; Dijkstra's Algorithm

(defun dijkstra (source weight-matrix)
  "Return the shortest path weights from SOURCE to other vertices of
given WEIGHT-MATRIX.  The result is a list."
  (let* ((len (length weight-matrix))
         (dist (make-list len 'inf))
         s q u)
    ;; dist[source] = 0
    (setcar (nthcdr source dist) 0)
    ;; build q
    (let ((i 0))
      (while (< i len)
        (setq q (cons i q)
              i (1+ i))))
    ;; loop through q
    (while q
      (setq u (extract-min q dist)
            q (delq u q)
            s (cons u s))               ; `s' is ornamental
      (dolist (v (adjacencies u weight-matrix))
        (when (numberp (nth u dist))    ; dist[u] != 'inf
          (let ((sum (+ (nth u dist)
                        (nth v (nth u weight-matrix)))))
            (when (or (not (numberp (nth v dist)))
                      (> (nth v dist)
                         sum))
              (setcar (nthcdr v dist) sum))))))
    dist))

;; Sample data
(unless (and (equal
              (dijkstra
               0
               '((inf 10 3 inf inf)
                 (inf inf 1 2 inf)
                 (inf 4 inf 8 2)
                 (inf inf inf inf 7)
                 (inf inf inf 9 inf)))
              '(0 7 3 9 5))
             (equal
              (dijkstra
               1
               '((inf 10 3 inf inf)
                 (inf inf 1 2 inf)
                 (inf 4 inf 8 2)
                 (inf inf inf inf 7)
                 (inf inf inf 9 inf)))
              '(inf 0 1 2 3)))
  (message "dijkstra: Consistency error"))

;;; Depth-First Search

(defvar dfs-time 0)

(defun dfs-visit (u color prev dist finish adjacencies)
  (setq dfs-time (1+ dfs-time))
  (setcar (nthcdr u color) 'gray)
  (setcar (nthcdr u dist) dfs-time)
  (dolist (v (nth u adjacencies))
    (when (eq (nth v color) 'white)
      (setcar (nthcdr v prev) u)
      (dfs-visit v color prev dist finish adjacencies)))
  (setcar (nthcdr u color) 'black)
  (setq dfs-time (1+ dfs-time))
  (setcar (nthcdr u finish) dfs-time))

(defun dfs (adjacencies &optional vertex-order)
  (let* ((len (1+ (length adjacencies)))
         (color (make-list len 'white))
         (prev (make-list len nil))
         (dist (make-list len 'inf))
         (finish (make-list len 'inf)))
    ;; we have to move everything up one due to fscking index-at-1
    (setq adjacencies (cons nil adjacencies))
    (setq dfs-time 0)
    ;; initialize vertex-order
    (unless vertex-order
      (let ((i 1))
        (while (<= i len)
          (setq vertex-order (cons i vertex-order))
          (setq i (1+ i))))
      (setq vertex-order (nreverse vertex-order)))
    ;; visit vertices
    (dolist (u vertex-order)
      (when (eq (nth u color) 'white)
        (dfs-visit u color prev dist finish adjacencies)))
    (list (cdr dist) (cdr finish) (cdr prev))))

;; Sample data
(unless (equal
         (dfs '((2)
                (3 4)
                (5 7)
                (1 5)
                (3)
                (3 7)
                (9)
                (7)
                (8)))
         '((1 2 3 13 4 17 6 8 7)
           (16 15 12 14 5 18 11 9 10)
           (nil 1 2 2 3 nil 3 9 7)))
  (message "dfs: Consistency error"))

(unless (equal
         (transpose-adjacencies
          '((2)
            (3 4)
            (5 7)
            (1 5)
            (3)
            (3 7)
            (9)
            (7)
            (8))
          '<)
         '((4)
           (1)
           (2 5 6)
           (2)
           (3 4)
           nil
           (3 6 8)
           (9)
           (7)))
  (message "transpose-adjacencies: Consistency error"))

;;; Strongly-Connected Components

(defun strongly-connected-components (adjacencies)
  "Find the strongly-connected components of the graph given in
ADJACENCIES, which is in the form of an adjacency list."
  ;; NOTE: This returns PREV (from the last DFS) rather than the
  ;; connected components, since I haven't perfected the
  ;; extract-forest routine yet.
  (let* ((len (length adjacencies))
         (dfs-result (dfs adjacencies))
         (finish-result (cons nil (nth 1 dfs-result)))
         finish-order)
    ;; sort and transpose the adjacenct vertexes by decreasing finish
    ;; result
    (setq adjacencies (transpose-adjacencies
                       adjacencies
                       #'(lambda (s1 s2)
                           (> (nth s1 finish-result)
                              (nth s2 finish-result)))))
    ;; compute finish order
    (let ((i 1))
      (while (<= i len)
        (setq finish-order (cons i finish-order))
        (setq i (1+ i))))
    (setq finish-order
          (sort finish-order
                #'(lambda (s1 s2)
                    (> (nth s1 finish-result)
                       (nth s2 finish-result)))))
    ;; call DFS
    (setq dfs-result (dfs adjacencies finish-order))
    ;; extract forest
;;    (extract-forest (nth 2 dfs-result))
    (nth 2 dfs-result)))

;; Sample data
(unless (equal
         (strongly-connected-components
          '((2)
            (3 4)
            (5 7)
            (1 5)
            (3)
            (3 7)
            (9)
            (7)
            (8)))
         '(nil 4 nil 1 3 nil nil 7 8))
  (message "strongly-connected-components: Consistency error"))

(provide 'algorithms)

;; algorithms.el ends here
