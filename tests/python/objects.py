from metalift.frontend.python import Driver
from metalift.objects import Int



if __name__ == "__main__":
    
    driver = Driver()
    
    i = Int(driver)
    j = Int(driver)
    print(f"sub: {i - j}")
    print(f"add: {i + j}")
    print(f"gt: {(i < j).And(j > 10)}")
