type ('i, 'o) test_data = {
  input: 'i;
  output: 'o
};;

val test :
  string ->
  tester:('i -> 'o) ->
  ?compare:('o -> 'o -> bool) ->
  string_of:('o -> string) ->
  ('i, 'o) test_data Stream.t ->
  int * int
