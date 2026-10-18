addpath('shims');
% Midpoint cases: 1 + 2^-24 is a tie; with a tiny extra it must round up.
assert(fma(single(1), 1, single(2^-24)) == single(1));
assert(fma(single(1), 1, 2^-24 + 2^-60) == single(1 + 2^-23));
assert(fma(single(1), 1, 2^-24 - 2^-60) == single(1));
assert(fma(single(-1), 1, -2^-24 - 2^-60) == single(-1 - 2^-23));
x = single(1 + 2^-23); y = single(2^-24);
assert(fma(x, 1, y) == single(1 + 2^-22));
assert(fma(single(-1), 1, single(-2^-24)) == single(-1));
disp('shim ok');
