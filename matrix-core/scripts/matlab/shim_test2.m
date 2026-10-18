addpath('shims');
assert(bitshift(uint64(12345), -135) == 0);
assert(bitshift(uint64(12345), -7) == uint64(96));
assert(isequal(bitshift(uint32([100 200]), -int16([0 15])), uint32([100 0])));
disp('bitshift shim ok');
