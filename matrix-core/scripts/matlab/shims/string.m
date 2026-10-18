function s = string(x)
% Octave stand-in for MATLAB's string(): the model only indexes rows of a char matrix with {}.
  s = cellstr(x);
end
