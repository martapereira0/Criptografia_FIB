import time
import pickle
import hashlib
import json
import random
import sympy
import math
import os
from Crypto.Util import number
from Crypto import Random
from cryptography.hazmat.primitives.asymmetric import rsa

LIMIT = pow(base=2, exp=(256-16))

"""
We shall use the pycryptodome package in Python to generate RSA keys
"""


class block:
    def __init__(self):
        """
        crea un bloque (no necesariamente válido)
        """
        self.block_hash = 0
        self.previous_block_hash = 0
        self.transaction = 0
        self.seed = 0
    
    def genesis(self,trans):
        """
        genera el primer bloque de una cadena con la transacción "transaction"
        que se caracteriza por:
        - previous_block_hash=0
        - ser válido
        """
        self.previous_block_hash = 0
        self.transaction = trans

        # generate seed and hash in loop until its a valid one 
        
        while True:
            self.seed = random.randint(0, 1 << 128) 
            self.block_hash = self.calculate_hash()
            if self.block_hash < LIMIT:
                break
        return self

    def calculate_hash(self):        
        
        """ Calculates the hash SHA256 of the current block. """

        entrada = str(self.previous_block_hash)
        entrada = entrada + str(self.transaction.public_key.publicExponent)
        entrada = entrada + str(self.transaction.public_key.modulus)
        entrada = entrada + str(self.transaction.message)
        entrada = entrada + str(self.transaction.signature)
        entrada = entrada + str(self.seed)
        h = int(hashlib.sha256(entrada.encode()).hexdigest(),16)
        return h        

    def next_block(self, trans):
        """
        genera un bloque válido seguiente al actual con la transaccion "transaction"
        """
        new_block = block()
        new_block.previous_block_hash = self.block_hash
        new_block.transaction = trans
        
        while True:
            new_block.seed = random.randint(0, 1 << 128)
            new_block.block_hash = new_block.calculate_hash()
            if new_block.block_hash < LIMIT:
                break
        return new_block


    def verify_block(self):
        """
        Verifica si un bloque es válido:
        -Comprueba que el hash del bloque anterior cumple las condiciones exigidas
        -Comprueba que la transacción del bloque es válida
        -Comprueba que el hash del bloque cumple las condiciones exigidas
        Salida: el booleano True si todas las comprobaciones son correctas;
        el booleano False en cualquier otro caso.
    
        Un bloque es válido si la transaccion es válida y su hash h satisface la condición h < 2^(256−d)
        siendo d un parametro que indica el proof of work necesario par generar un bloque válido. Para esta practica d=16
        """
        
        
        k = self.previous_block_hash
        if (k >= LIMIT):
            return False
        
        if (self.transaction.verify() == False):
            return False

        current_block_hash_value = self.block_hash

        if (current_block_hash_value >= LIMIT):
            return False        
        return True

class transaction:

    def __init__(self, message, RSAkey,use_slow_sign): 
        """
        genera una transaccion firmando "message" con la clave "RSAkey"
        """
        self.public_key = rsa_public_key(RSAkey) 
        self.message = message
        if use_slow_sign:
            self.signature = RSAkey.sign_slow(message)
        else:
            self.signature = RSAkey.sign(message)

    def verify(self):
        """
        Salida: el booleano True si "signature" se corresponde con la
        firma de "message" hecha con la clave RSA asociada a la clave
        pública RSA;
        el booleano False en cualquier otro caso.
        """
        return self.public_key.verify(self.message,self.signature)
        
def calculate_hash(transaction: transaction, previous_block_hash: int, seed: int):
    entrada=str(previous_block_hash)
    entrada=entrada+str(transaction.public_key.publicExponent)
    entrada=entrada+str(transaction.public_key.modulus)
    entrada=entrada+str(transaction.message)
    entrada=entrada+str(transaction.signature)
    entrada=entrada+str(seed)
    h=int(hashlib.sha256(entrada.encode()).hexdigest(),16)
    return h

class rsa_key:

    def __init__(self, bits_modulo=2048, e=2**16+1):
        private_key = rsa.generate_private_key(public_exponent=e, key_size=bits_modulo)
        key = private_key.private_numbers()

        self.bits_modulo = bits_modulo
        self.publicExponent = e 
        self.primeP = key.p
        self.primeQ = key.q 
        # self.generatePQ() 
        self.modulus = self.primeP * self.primeQ # n = p * q
        phi_n = (self.primeP - 1) * (self.primeQ - 1)
        
        """
        self.privateExponent = number.inverse(self.publicExponent,(self.primeP - 1) * (self.primeQ - 1)) # d≡e^-1(mod ϕ(n))
        self.inverseQModulusP = number.inverse(self.primeP,self.primeQ)
        self.privateExponentModulusPhiP = number.inverse(self.privateExponent, self.primeP - 1)
        self.privateExponentModulusPhiQ = number.inverse(self.privateExponent, self.primeQ - 1)
        """
        self.privateExponent = (sympy.gcdex(self.publicExponent, phi_n)[0]) % ((self.primeP-1)*(self.primeQ-1))
        self.inverseQModulusP = sympy.gcdex(self.primeQ,self.primeP)[0]
        self.privateExponentModulusPhiP = self.privateExponent % (self.primeP - 1)
        self.privateExponentModulusPhiQ = self.privateExponent % (self.primeQ - 1)
    
    """
    This two functions are not used in the code, but it is here to show how we could generate p and q
    """
    def generatePQ(self):
        """ p e q são primos aleatórios com N bits """
        valid = 0 
        while (valid == 0):
            self.primeP = number.getPrime(self.bits_modulo, randfunc=Random.get_random_bytes)
            self.primeQ = number.getPrime(self.bits_modulo, randfunc=Random.get_random_bytes)
            valid = self.validatePQ()
    
    def validatePQ(self):
        """ p e q são válidos se p!=q e mcd(e,(p-1)(q-1)) = 1 """
        return self.primeP != self.primeQ and math.gcd(self.publicExponent,(self.primeP - 1)*(self.primeQ -1))

    def sign(self,message):
        """
        Salida: un entero que es la firma de "message" hecha con la clave RSA usando el TCR
        """
        """
        Para assinar pow(m,d,n) é muito lento pq d é muito grande então para tornar d mais pequeno: m^d =m^d mod(p-1)(q-1)
        então: pow(m,d%(p-1)(q-1),n).
        Sabemos que a mod p.q pode ser dividido em: a mod p ; a mod q.
        Assim, temos que d%(p-1)(q-1) : a_1 = d mod (p-1) e a_2 = d mod (q-1) e a = (a_1*q'*q + a_2*p'*p) % n
        """
        a_1 = int(self.privateExponentModulusPhiP)  # a_1 = self.privateExponent % (self.primeP - 1)
        
        a_2 = int(self.privateExponentModulusPhiQ) # a_2 = self.privateExponent % (self.primeQ - 1)

        # gcdex(self.primeP,self.primeQ) = p',q',1
        p_inv = sympy.gcdex(self.primeP,self.primeQ)[0] # p'
        q_inv = sympy.gcdex(self.primeP,self.primeQ)[1] # q'
        # p_inv = number.inverse(self.primeP,self.primeQ) 
        # q_inv = number.inverse(self.primeQ,self.primeP) 

        c_1 = pow(message, a_1, self.primeP)
        c_2 = pow(message, a_2, self.primeQ)

        return (c_1 * q_inv * self.primeQ + c_2 * p_inv * self.primeP) % self.modulus


    def sign_slow(self,message):
        """
        m^d % n
        Salida: un entero que es la firma de "message" hecha con la clave RSA sin usar el TCR
        """
        message = int(message)
        return pow(message,int(self.privateExponent),int(self.modulus))


class rsa_public_key:

    def __init__(self, rsa_key):
        """
        genera la clave pública RSA asociada a la clave RSA "rsa_key"
        """
        self.publicExponent = rsa_key.publicExponent
        self.modulus = rsa_key.modulus

    def verify(self, message, signature):
        """
        Salida: el booleano True si "signature" se corresponde con la
        firma de "message" hecha con la clave RSA asociada a la clave
        pública RSA;
        el booleano False en cualquier otro caso.

        https://cryptobook.nakov.com/digital-signatures/rsa-sign-verify-examples
        """
        return pow(signature,self.publicExponent,self.modulus) == message


class block_chain:

    def __init__(self,transaction):
        """
        genera una cadena de bloques que es una lista de bloques,
        el primer bloque es un bloque "genesis" generado amb la transaccio "transaction"
        """
        new_block = block()
        self.list_of_blocks = [new_block.genesis(transaction)] 

    def add_block(self,transaction):
        """
        a~nade a la cadena un nuevo bloque valido generado con la transacci´on "transaction"
        """
        new_block = self.list_of_blocks[-1].next_block(transaction) # create a new block
        self.list_of_blocks.append(new_block) # add it to the chain

    def verify(self):    
        """
        verifica si la cadena de bloques es valida:
        - Comprueba que todos los bloques son validos
        - Comprueba que el primer bloque es un bloque "genesis"
        - Comprueba que para cada bloque de la cadena el siguiente es correcto
        Salida: el booleano True si todas las comprobaciones son correctas;
        en cualquier otro caso, el booleano False y un entero
        correspondiente al ultimo bloque valido
        """
    
        # Verifies if the first block is a "genesis" block, the first block is a "genesis" block if its previous block is 0
        first_block = self.list_of_blocks[0]
        if not first_block.verify_block() or first_block.previous_block_hash != 0:
            return False, 0


        for i in range(0, len(self.list_of_blocks) - 1):
            current_block = self.list_of_blocks[i] 
            next_block = self.list_of_blocks[i + 1] 

            if not current_block.verify_block():
                return False, i

            # Verifies if the current block correctly points to the next block and if the hash of the current block is equal to the hash of the previous block with the transaction and seed
            h = calculate_hash(next_block.transaction,current_block.block_hash,next_block.seed)
            if current_block.block_hash != next_block.previous_block_hash or h != next_block.block_hash:
                return False, i
        # All checks passed, the blockchain is valid
        return True


def read_block_chain(filename):
    with open(filename, 'rb') as file:
        instance_read = pickle.load(file)
    return instance_read

def write_block_chain(filename, instance):
    with open(filename, 'wb') as file:
        pickle.dump(instance, file)

def test_files():
    def check(expected):
        b1 = read_block_chain(filename)
        result,_ = b1.verify()
        if (result == expected) :
            print(f"Test {filename} passed.") 
        else:
            print(f"Test {filename} failed.")

    filename = "Cadena_bloques_bloque_falso.block"
    check(False)

    filename = "Cadena_bloques_seed_falsa.block"
    check(False)

    filename = "Cadena_bloques_transaccion_falsa.block"
    check(False)

    filename = "Cadena_bloques_valida.block"
    check(True)
      
def create_random_trans(n):
    transactions = []
    for _ in range(n):
        message = random.randrange(0, 2**128)
        RSAkey = rsa_key(bits_modulo=2048, e=2**16+1)
        new_transaction = transaction(message, RSAkey, False)
        transactions.append(new_transaction)
    return transactions

def visualize_block_chain(filename):
    block_chain = read_block_chain(filename)
    print("Loaded Block Chain:\n")
    for block in block_chain.list_of_blocks:
        print(f"Block {block_chain.list_of_blocks.index(block)}:")
        print(f"Previous block hash: {block.previous_block_hash}")
        print(f"Block hash: {block.block_hash}")
        print(f"Seed: {block.seed}")
        print(f"Transaction:")
        # print(f"Public key:")
        print(".......................")
        print(f"Public exponent: {block.transaction.public_key.publicExponent}")
        print(f"Modulus: {block.transaction.public_key.modulus}")
        print(f"Message: {block.transaction.message}")
        print(f"Signature: {block.transaction.signature}")
        print("Verificar transação e bloco:")
        print(f"Verify: {block.transaction.verify()}")
        print(f"Verify block: {block.verify_block()}")
        print("--------------------------------------------------")


def create_block_chain(n):
    """
    Creates a valid block chain with n blocks and write the block chain in a file
    """
    print(f"Creating a block chain with {n} blocks.")
    transactions = create_random_trans(n)
    block = block_chain(transactions[0])
    for i in range(1,n):
        block.add_block(transactions[i])
        # if not block.verify():
            # print(f"Error: A blockchain is not valid after adding the transaction {i}.")

    if block.verify():
        write_block_chain(f"block_chain_{n}_valid_blocks.block", block)
        # visualize_block_chain(f"block_chain_valid_{n}.block")


def create_block_chain_with_invalid_blocks(n,m):
    """
    Creates a block chain with n blocks but only m of them are valid
    """
    print(f"Creating a block chain with {n} blocks but only {m} of them are valid.")
    transactions = create_random_trans(n)
    block = block_chain(transactions[0])
    for i in range(1,n):
        block.add_block(transactions[i])
        if i == m + 1: # basta alterar o hash do bloco m+1 para que o bloco m+2 seja inválido e por aí fora
            block.list_of_blocks[-1].previous_block_hash = block.list_of_blocks[-2].previous_block_hash + 1
            # block.list_of_blocks[i-1].previous_block_hash = (2**256)+1
    if not block.verify() == (m <= n):
        print(f"Error: Blockchain verification failed.")
    write_block_chain(f"block_chain_{m}_valid_blocks.block", block)
    # visualize_block_chain(f"block_chain_{m}_blocks_valid.block")


def required_time(function):
    """
    Measure the time it takes to execute a function
    """
    start = time.perf_counter()
    function()
    end = time.perf_counter()
    return end-start



if __name__ == "__main__":
    start = time.perf_counter()
    create_block_chain(100)
    # create_block_chain_with_invalid_blocks(100, 42)
    end = time.perf_counter()
    print(f"Time elapsed: {end-start} seconds .")
    # print(test_files())
    # print(read_block_chain("Cadena_bloques_bloque_falso.block").verify())

def main():
    print("main")