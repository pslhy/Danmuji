class ParseException(Exception):
    def __init__(self, func_name, message):
        self.func_name = func_name
        self.message = message
    def __str__(self):
        return "Error at " + self.func_name + ": " + self.message