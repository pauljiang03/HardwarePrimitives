function r = dot(a, b)
% MATLAB dot semantics: two empty vectors of any shape give 0 (Octave rejects 0x0 with 1x0).
  if isempty(a) && isempty(b)
    r = 0;
  else
    r = builtin('dot', a, b);
  end
end
