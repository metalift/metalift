from enum import Enum


class Backend(Enum):
    NUMPY = 1
    TENSORFLOW = 2
    PYTORCH = 3


class DataType(Enum):
    # TODO: add documentation
    FLOAT = "float"
    UINT_8 = "int"  # do we want to name this uint8?
    INT32 = "int32"
