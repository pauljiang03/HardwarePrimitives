function driver(model_dir, infile, outfile, variant)
% Evaluate inner products with the MATLAB Tensor Core v0.6 matrix-core model.
%
% Each input line is: model k a_1 ... a_k b_1 ... b_k c, with values as hexadecimal binary64
% (num2hex) words. Blocks are chained as in models/tools/GEMM.m: the vectors are padded with
% zeros to a multiple of N_FMA and each block's output is the next block's c. The output line is
% the hexadecimal binary64 word of d.
%
% variant = 'shipped' uses the parameters exactly as in MI100MC.m, MI210MC.m and MI300AMC.m.
% variant = 'rdfix' additionally sets the field rd_borrow_carry, so that Generic_BFMA_TC.m reads
% MI300AMC.m's rd_norm_aware flag (line 54) and executes the RD of S_acc.
  addpath(fullfile(model_dir, 'models', 'tools'));
  warning('off', 'Octave:shadowed-function');
  addpath(fullfile(fileparts(mfilename('fullpath')), 'shims'));
  fin = fopen(infile, 'r');
  fout = fopen(outfile, 'w');
  while true
    line = fgetl(fin);
    if ~ischar(line), break; end
    t = strsplit(strtrim(line), ' ');
    prof = t{1};
    k = str2double(t{2});
    v = hex2num(t(3:end));
    a = v(1:k)'; b = v(k + 1:2 * k)'; c = v(2 * k + 1);
    p = params(prof, variant);
    n = p.fma;
    pad = mod(n - mod(k, n), n);
    a = [a, zeros(1, pad)]; b = [b, zeros(1, pad)];
    for j = 1:(numel(a) / n)
      c = Generic_BFMA_TC(a((j - 1) * n + 1:j * n), b((j - 1) * n + 1:j * n), c, p);
    end
    fprintf(fout, '%s\n', num2hex(double(c)));
  end
  fclose(fin);
  fclose(fout);
end

function p = params(prof, variant)
  % Defaults shared by the model files.
  p.frmode = 'rne'; p.armode = 'rd'; p.stkbitenabled = 0;
  p.global_alignment = 0; p.late_partial_sum = 0; p.odd_even_grouping = 0;
  p.pair_wise_sum = 0; p.denorm_prd = 0; p.min_exp_limit = -1024; p.c_min_exp_limit = 0;
  p.prd_limit = 0; p.correct_rounding = 0; p.in_subnormals = 1; p.out_subnormals = 1;
  p.fp8_fnuz = 0; p.NoManBitsOut = 23; p.NoExpBitsOut = 8;
  switch prof
    case {'cdna1F16', 'cdna1BF16'}            % MI100MC.m
      p.fma = 4; p.neab = Inf; p.correct_rounding = 1;
      if strcmp(prof, 'cdna1BF16'), p.fma = 2; end
    case {'cdna2F16', 'cdna2BF16', 'cdna2BF16_1k'}  % MI210MC.m (group size per instruction)
      p.fma = 4; p.neab = Inf; p.pair_wise_sum = 1; p.prd_limit = 1;
      p.in_subnormals = 0; p.out_subnormals = 0;
      if strcmp(prof, 'cdna2BF16'), p.fma = 2; end
    otherwise                                  % MI300AMC.m
      p.fma = 8; p.neab = 1; p.rd_norm_aware = 1; p.global_alignment = 1;
      p.late_partial_sum = 1; p.denorm_prd = 1; p.c_min_exp_limit = 1; p.prd_limit = 1;
      if strcmp(prof, 'cdna3XF32'), p.fma = 4; end
      if any(strcmp(prof, {'cdna3E4M3', 'cdna3E5M2'}))
        p.global_alignment = 0; p.fp8_fnuz = 1; p.fma = 16; p.odd_even_grouping = 1;
      end
      if strcmp(variant, 'rdfix'), p.rd_borrow_carry = 1; end
  end
  switch prof
    case {'cdna1F16', 'cdna2F16', 'cdna3F16'}, p.NoExpBitsIn = 5; p.NoManBitsIn = 10;
    case {'cdna1BF16', 'cdna2BF16', 'cdna2BF16_1k', 'cdna3BF16'}, p.NoExpBitsIn = 8; p.NoManBitsIn = 7;
    case 'cdna3XF32', p.NoExpBitsIn = 8; p.NoManBitsIn = 10;
    case 'cdna3E4M3', p.NoExpBitsIn = 4; p.NoManBitsIn = 3;
    case 'cdna3E5M2', p.NoExpBitsIn = 5; p.NoManBitsIn = 2;
  end
end
