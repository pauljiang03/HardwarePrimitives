// @ts-check
import { defineConfig } from 'astro/config';
import starlight from '@astrojs/starlight';

export default defineConfig({
  site: 'https://pauljiang03.github.io',
  base: '/HardwarePrimitives',
  trailingSlash: 'always',
  devToolbar: { enabled: false },
  // Old URLs (renamed pages) forward to their current pages.
  redirects: {
    '/overview': '/HardwarePrimitives/',
    '/model/conversion': '/HardwarePrimitives/model/normalization/',
    '/proofs/trust': '/HardwarePrimitives/proofs/tested/',
    '/model/profiles': '/HardwarePrimitives/model/variants/',
    '/amd/getting-started': '/HardwarePrimitives/quick-start/',
    '/amd/notation': '/HardwarePrimitives/amd/formats/',
    '/amd/architectures': '/HardwarePrimitives/amd/',
    '/amd/theorems': '/HardwarePrimitives/proofs/theorems/',
  },
  integrations: [
    starlight({
      title: 'Hardware Primitives',
      description:
        'Lean 4 models of the matrix multipliers of NVIDIA Tensor Cores (Volta to Blackwell) and AMD matrix cores (CDNA 1 to 3), and their proved properties: error bounds, non-monotonicity, TC-EFT and MC-EFT.',
      customCss: ['./src/styles/theme.css'],
      expressiveCode: {
        themes: ['github-dark-dimmed', 'github-light'],
        styleOverrides: { borderRadius: '2px', frames: { shadowColor: 'transparent' } },
      },
      social: [{ icon: 'github', label: 'GitHub', href: 'https://github.com/pauljiang03/HardwarePrimitives' }],
      sidebar: [
        {
          label: 'Start here',
          items: [
            { label: 'Overview', link: '/' },
            { label: 'Quick start', slug: 'quick-start' },
            { label: 'Project status', slug: 'status' },
          ],
        },
        {
          label: 'Modeling NVIDIA Tensor Cores',
          items: [
            { label: 'The model at a glance', slug: 'model' },
            { label: '1. Formats and decoding', slug: 'model/formats' },
            { label: '2. Exact products in denormalized form', slug: 'model/products' },
            { label: '3. Alignment', slug: 'model/alignment' },
            { label: '4. Accumulation', slug: 'model/accumulation' },
            { label: '5. Normalization and final rounding', slug: 'model/normalization' },
            { label: '6. Variants and their numerical features', slug: 'model/variants' },
            { label: '7. Instructions and chaining', slug: 'model/instructions' },
            { label: '8. Independent specification', slug: 'model/specification' },
            { label: '9. Bitvector datapath', slug: 'model/datapath' },
            { label: '10. Hardware validation', slug: 'model/validation' },
            { label: 'Modeling scope and limits', slug: 'model/scope' },
          ],
        },
        {
          label: 'Properties of Tensor Cores',
          items: [
            { label: 'Error bounds', slug: 'properties/error-bounds' },
            { label: 'Non-monotonicity', slug: 'properties/non-monotonicity' },
            { label: 'TC-EFT correction', slug: 'properties/eft' },
          ],
        },
        {
          label: 'Modeling AMD matrix cores',
          items: [
            { label: 'The model at a glance', slug: 'amd' },
            { label: '1. Formats and decoding', slug: 'amd/formats' },
            { label: '2. Exact products in denormalized form', slug: 'amd/products' },
            { label: '3. CDNA 1: correct rounding', slug: 'amd/cdna1' },
            { label: '4. CDNA 2: pairwise sums', slug: 'amd/cdna2' },
            { label: '5. CDNA 3: global alignment', slug: 'amd/cdna3' },
            { label: '6. Normalization and final rounding', slug: 'amd/normalization' },
            { label: '7. Instructions and chaining', slug: 'amd/instructions' },
            { label: '8. Independent specification', slug: 'amd/specification' },
            { label: '9. Hardware validation', slug: 'amd/validation' },
            { label: 'Modeling scope and limits', slug: 'amd/scope' },
          ],
        },
        {
          label: 'Properties of matrix cores',
          items: [
            { label: 'CDNA 1', slug: 'amd/properties/cdna1' },
            { label: 'CDNA 2', slug: 'amd/properties/cdna2' },
            { label: 'CDNA 3', slug: 'amd/properties/cdna3' },
            { label: 'MC-EFT correction', slug: 'amd/properties/eft' },
          ],
        },
        {
          label: 'Proofs & trust',
          items: [
            { label: 'What is proven', slug: 'proofs/theorems' },
            { label: 'What is tested', slug: 'proofs/tested' },
            { label: 'FloatLib cross-check', slug: 'proofs/floatlib' },
          ],
        },
        {
          label: 'Reference',
          items: [
            { label: 'Commands', slug: 'reference/commands' },
            { label: 'Repository layout', slug: 'reference/layout' },
          ],
        },
      ],
    }),
  ],
});
