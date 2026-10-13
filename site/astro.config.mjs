// @ts-check
import { defineConfig } from 'astro/config';
import starlight from '@astrojs/starlight';

export default defineConfig({
  site: 'https://pauljiang03.github.io',
  base: '/TC-EFT',
  trailingSlash: 'always',
  devToolbar: { enabled: false },
  // Old URLs (renamed pages) forward to their current pages.
  redirects: {
    '/overview': '/TC-EFT/',
    '/model/conversion': '/TC-EFT/model/normalization/',
    '/proofs/trust': '/TC-EFT/proofs/tested/',
    '/model/profiles': '/TC-EFT/model/variants/',
  },
  integrations: [
    starlight({
      title: 'TC-EFT',
      description:
        'A Lean 4 model of NVIDIA Tensor Core block arithmetic, its non-monotonicity, and the TC-EFT correction algorithm.',
      customCss: ['./src/styles/theme.css'],
      expressiveCode: {
        themes: ['github-dark-dimmed', 'github-light'],
        styleOverrides: { borderRadius: '2px', frames: { shadowColor: 'transparent' } },
      },
      social: [{ icon: 'github', label: 'GitHub', href: 'https://github.com/pauljiang03/TC-EFT' }],
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
          label: 'Modeling the Tensor Core',
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
          label: 'Modeling AMD matrix cores',
          items: [
            { label: 'The AMD model at a glance', slug: 'amd' },
            { label: '1. Getting started', slug: 'amd/getting-started' },
            { label: '2. Notation and formats', slug: 'amd/notation' },
            { label: '3. The three architectures', slug: 'amd/architectures' },
            { label: '4. Independent specification', slug: 'amd/specification' },
            { label: '5. What is proved', slug: 'amd/theorems' },
            { label: '6. Validation', slug: 'amd/validation' },
            { label: 'Modeling scope and limits', slug: 'amd/scope' },
          ],
        },
        {
          label: 'Properties & algorithms',
          items: [
            { label: 'Error bounds', slug: 'properties/error-bounds' },
            { label: 'Non-monotonicity', slug: 'properties/non-monotonicity' },
            { label: 'TC-EFT correction', slug: 'properties/eft' },
          ],
        },
        {
          label: 'Ozaki schemes',
          items: [
            { label: 'At a glance', slug: 'ozaki' },
            { label: 'Ozaki-I, proved end to end', slug: 'ozaki/ozaki-1' },
            { label: 'Ozaki-II, proved end to end', slug: 'ozaki/ozaki-2' },
            { label: 'ADP and ESC', slug: 'ozaki/adp' },
            { label: 'Correct rounding', slug: 'ozaki/correct-rounding' },
            { label: 'What the hardware semantics give', slug: 'ozaki/hardware' },
            { label: 'Related work and novelty', slug: 'ozaki/literature' },
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
