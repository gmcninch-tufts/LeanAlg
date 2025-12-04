
def path : System.FilePath := System.mkFilePath ["foo.txt"]

def f : IO String := IO.FS.readFile path

#eval f

