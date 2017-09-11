section
parameter P : match unit.star with
| unit.star := true
end

include P

example : false :=
begin
  dsimp [_match_1] at P,
  guard_hyp P := true,
  admit
end
end

section
parameter P : match unit.star with
| unit.star := true
end

include P

example : false :=
begin
  dsimp [_match_1] at P,
  guard_hyp P := true,
  admit
end
end
