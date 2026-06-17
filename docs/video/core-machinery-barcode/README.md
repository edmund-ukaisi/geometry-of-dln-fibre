# Core Machinery Barcode Video

This directory contains a silent Manim video explaining the core type-A quiver
machinery behind the multiplication map of composable matrix tuples.

## Contents

- `storyboard.md` - scene-by-scene narrative and visual plan.
- `core_machinery_barcode.py` - Manim source.
- `renders/final/` - final exported MP4 target.
- `.venv/` and `media/` - local generated environment/cache, ignored.

## Render

From this directory:

```bash
.venv/bin/manim -ql --fps 30 --media_dir media core_machinery_barcode.py CoreMachineryBarcode
```

Final 1080p render:

```bash
.venv/bin/manim -qh --fps 30 --media_dir media core_machinery_barcode.py CoreMachineryBarcode
cp media/videos/core_machinery_barcode/1080p30/CoreMachineryBarcode.mp4 renders/final/core-machinery-barcode-1080p.mp4
```

The video is intentionally silent. The narrative is carried by on-screen
captions and formulas.
