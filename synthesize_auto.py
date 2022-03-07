import os

if os.environ.get("SYNTH_CVC5") == "1":
    from synthesize_cvc5 import synthesize
else:
    from synthesize_rosette import synthesize
