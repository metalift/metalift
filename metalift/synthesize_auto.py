import os

if os.environ.get("SYNTH_CVC5") == "1":
    from metalift.synthesize_cvc5 import synthesize
else:
    from metalift.rosette.synthesize_rosette import synthesize
