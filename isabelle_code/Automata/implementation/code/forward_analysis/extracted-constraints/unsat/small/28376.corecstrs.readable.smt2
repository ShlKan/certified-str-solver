

var_0xINPUT_124514 in {
initial state: 0
state 0 [accept]:
};

var_0xINPUT_124514 in {
initial state: 1
state 0 [reject]:
  \u0000-\uffff -> 2
state 1 [accept]:
  - -> 0
  \u0000-, -> 2
  .-\uffff -> 2
state 2 [accept]:
  \u0000-\uffff -> 2
};
