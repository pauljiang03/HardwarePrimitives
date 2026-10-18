// @ts-check
import { defineConfig } from 'astro/config';
import starlight from '@astrojs/starlight';

// Pages moved from /model/, /properties/ and /amd/ to sections named after the repository folders.
const moved = (from, to, pages) =>
  Object.fromEntries(pages.map((page) => [
    `/${from}${page && `/${page}`}`,
    `/HardwarePrimitives/${to}/${page && `${page}/`}`,
  ]));

export default defineConfig({
  site: 'https://pauljiang03.github.io',
  base: '/HardwarePrimitives',
  trailingSlash: 'always',
  devToolbar: { enabled: false },
  // Old URLs forward to their current pages.
  redirects: {
    '/overview': '/HardwarePrimitives/',
    '/proofs/trust': '/HardwarePrimitives/proofs/tested/',
    '/model/conversion': '/HardwarePrimitives/tensor-core/normalization/',
    '/model/profiles': '/HardwarePrimitives/tensor-core/variants/',
    '/amd/getting-started': '/HardwarePrimitives/quick-start/',
    '/amd/notation': '/HardwarePrimitives/matrix-core/formats/',
    '/amd/architectures': '/HardwarePrimitives/matrix-core/',
    '/amd/theorems': '/HardwarePrimitives/proofs/theorems/',
    ...moved('model', 'tensor-core', ['', 'formats', 'products', 'alignment', 'accumulation', 'normalization',
      'variants', 'instructions', 'specification', 'datapath', 'validation', 'scope']),
    ...moved('properties', 'tensor-core/properties', ['error-bounds', 'non-monotonicity', 'eft']),
    ...moved('amd', 'matrix-core', ['', 'formats', 'products', 'cdna1', 'cdna2', 'cdna3', 'normalization',
      'instructions', 'specification', 'validation', 'scope', 'properties/cdna1', 'properties/cdna2',
      'properties/cdna3', 'properties/eft']),
  },
  integrations: [
    starlight({
      title: 'Hardware Primitives',
      description:
        'Lean 4 models of the matrix multipliers of NVIDIA Tensor Cores (Volta to Blackwell) and AMD Matrix Cores (CDNA 1 to 3), and their proven properties: error bounds, non-monotonicity, TC-EFT and MC-EFT.',
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
            { label: 'The model at a glance', slug: 'tensor-core' },
            { label: '1. Formats and decoding', slug: 'tensor-core/formats' },
            { label: '2. Exact products in denormalized form', slug: 'tensor-core/products' },
            { label: '3. Alignment', slug: 'tensor-core/alignment' },
            { label: '4. Accumulation', slug: 'tensor-core/accumulation' },
            { label: '5. Normalization and final rounding', slug: 'tensor-core/normalization' },
            { label: '6. Variants and their numerical features', slug: 'tensor-core/variants' },
            { label: '7. Instructions and chaining', slug: 'tensor-core/instructions' },
            { label: '8. Independent specification', slug: 'tensor-core/specification' },
            { label: '9. Bitvector datapath', slug: 'tensor-core/datapath' },
            { label: '10. Hardware validation', slug: 'tensor-core/validation' },
            { label: 'Modeling scope and limits', slug: 'tensor-core/scope' },
          ],
        },
        {
          label: 'Properties of Tensor Cores',
          items: [
            { label: 'Error bounds', slug: 'tensor-core/properties/error-bounds' },
            { label: 'Non-monotonicity', slug: 'tensor-core/properties/non-monotonicity' },
            { label: 'TC-EFT correction', slug: 'tensor-core/properties/eft' },
          ],
        },
        {
          label: 'Modeling AMD Matrix Cores',
          items: [
            { label: 'The model at a glance', slug: 'matrix-core' },
            { label: '1. Formats and decoding', slug: 'matrix-core/formats' },
            { label: '2. Exact products in denormalized form', slug: 'matrix-core/products' },
            { label: '3. CDNA 1: correct rounding', slug: 'matrix-core/cdna1' },
            { label: '4. CDNA 2: pairwise sums', slug: 'matrix-core/cdna2' },
            { label: '5. CDNA 3: global alignment', slug: 'matrix-core/cdna3' },
            { label: '6. Normalization and final rounding', slug: 'matrix-core/normalization' },
            { label: '7. Instructions and chaining', slug: 'matrix-core/instructions' },
            { label: '8. Independent specification', slug: 'matrix-core/specification' },
            { label: '9. Hardware validation', slug: 'matrix-core/validation' },
            { label: 'Modeling scope and limits', slug: 'matrix-core/scope' },
          ],
        },
        {
          label: 'Properties of Matrix Cores',
          items: [
            { label: 'CDNA 1', slug: 'matrix-core/properties/cdna1' },
            { label: 'CDNA 2', slug: 'matrix-core/properties/cdna2' },
            { label: 'CDNA 3', slug: 'matrix-core/properties/cdna3' },
            { label: 'MC-EFT correction', slug: 'matrix-core/properties/eft' },
          ],
        },
        {
          label: 'Proofs & trust',
          items: [
            { label: 'What is proven', slug: 'proofs/theorems' },
            { label: 'What is tested', slug: 'proofs/tested' },
            { label: 'Tensor Cores and Matrix Cores compared', slug: 'proofs/cross-vendor' },
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
