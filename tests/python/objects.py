from metalift.frontend.python import Driver
from metalift.objects import Int, List



if __name__ == "__main__":
    
    driver = Driver()
    
    i = Int(driver, "i")
    j = Int(driver, "j")
    print(f"i - j: {i - j}")
    print(f"i + j (rosette): {(i+j).toRosette()}")
    print(f"i + j: {i + j}")
    print(f"i == j: {i == j}")
    print(f"i > j & j > 10: {(i < j).And(j > 10)}")
    
    print(f"empty: {List.empty(driver, Int)}")
    l = List(driver, Int, "l")
    print(f"l: {l}")
    print(f"len(l): {l.len()}")
    print(f"l + l: {(l + l)}")
    print(f"l == l: {l == l}")
    print(f"l[0]: {l[0]}")

    # mutations
    l[0] = i
    print(f"l[0] = i: {l}")
    l.append(j)
    print(f"l.append(j): {l}")

    # list of lists
    l2 = List(driver, List[Int], "l2")
    print(f"l2: {l2}")
    print(f"l2[0]: {l2[0]}")
