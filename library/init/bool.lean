-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
prelude
import init.datatypes

attribute [inline]
definition {u} cond {A : Type u} : Bool → A → A → A
| tt a b := a
| ff a b := b

attribute [inline]
definition bor : Bool → Bool → Bool
| tt _  := tt
| ff tt := tt
| ff ff := ff

attribute [inline]
definition band : Bool → Bool → Bool
| ff _  := ff
| tt ff := ff
| tt tt := tt

attribute [inline]
definition bnot : Bool → Bool
| tt := ff
| ff := tt

notation a || b := bor a b
notation a && b := band a b
