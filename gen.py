import sys



n = int(sys.argv[1])



print("{\"orig\": [")



for i in range(0, n - 1):

    print("[150, 93, 200],[45, 239, 97],")



print("[150, 93, 200],[45, 239, 97]")



print("],")



print("\"gray\" : [")



for i in range(0, n - 1):

    print("122, 165,")



print("122, 165")



print("],")



print("\"negativeRemainder\" : [")



for i in range(0, n - 1):

    print("13, 0,")



print("13, 0")



print("],")



print("\"positiveRemainder\" : [")



for i in range(0, n - 1):

    print("0, 18,")



print("0, 18")





print("]}")


