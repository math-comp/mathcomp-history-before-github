Require Import ssreflect ssrbool.
Goal forall x, x && true = x.
move=> x.
rewrite [X in _ && _]andbT.
