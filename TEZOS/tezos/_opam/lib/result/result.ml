# 1 "result-as-alias.ml"
type ('a, 'b) result = ('a, 'b) Pervasives.result = Ok of 'a | Error of 'b
