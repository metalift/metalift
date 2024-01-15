import os

# pragma: no autoflake
if os.environ.get("SYNTH_CVC5") == "1":
    from metalift.synthesize_cvc5 import synthesize  # noqa
else:
    from metalift.synthesize_rosette import synthesize  # noqa
