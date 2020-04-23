#!/usr/bin/python3

import requests
import re
import gmpy2
import binascii 
import argparse
import os
import sys
import base64
import time
import struct
import sympy
import Crypto.PublicKey.RSA as RSA
from pyfiglet import Figlet
from clint.textui import puts, colored, indent
from Crypto.Util.number import *
from fractions import gcd
from bs4 import BeautifulSoup

def b32(enc):
	cipher="".join(enc.split())
	cipher=base64.b32decode(cipher)
	return cipher.decode('UTF-8')

def b64(enc):
	cipher="".join(enc.split())
	result=None
	for i in range(0,20):
		try:
			cipher=base64.b64decode(cipher + "===").decode('UTF-8')
		except:
			break
	return cipher			

def b85(enc):
	cipher=enc.encode('UTF-8')
	dec=base64.a85decode(cipher)
	return dec.decode('UTF-8')


def hextotext(enc):
	if enc.startswith('0x'):
		hex_string = enc[2:]
	else:
		hex_string=enc
	bytes_object = bytes.fromhex(hex_string)
	ascii_string = bytes_object.decode("ASCII")
	return ascii_string	

def dectotext(enc):
	string=''
	deci=enc.split()
	for i in deci:
		string+=chr(int(i))
	return string
		
def octtotext(enc):
	string=''
	oc=enc.split()
	for c in oc:
		string+=chr(int(c,8))
	return string

def bintotext(enc):
	bword=[enc[i:i+8] for i in range(0,len(enc),8)]
	string=''
	for ch in bword:
		a=int(ch,2)
		a=chr(a)
		string+=a
	return string


def cuberootrsa(n,e,c):
	#enc str type
	if e!=3:
		print("\033[1;31;40m [+] Value of e should be 3 in Cube Root RSA\n")
	def cuberoot(x):
		c,c1=None,2
		while c!=c1:
			c=c1
			c3=c**3
			d=(2*c3+x)
			c1=(c*(c3+2*x)+d//2)//d
		return c	
	cn=cuberoot(n)
	cc=cuberoot(c)
	if cc < cn :
		flag=repr(binascii.unhexlify(hex(cc)[2:]))
		return flag[2:]
	else:
		print("\033[1;31;40m [+] Error. Cube Root Of C is Not Less Than Cube Root Of N\n")	

def twinprime(n1,n2,c,e):
	def crack(n):
	    url_1='http://factordb.com/index.php?query=%i'
	    url_2 ='http://factordb.com/index.php?id=%s'
	    s = requests.Session()
	    r = s.get(url_1 %n, verify=False)
	    regex = re.compile("index\.php\?id\=([0-9]+)", re.IGNORECASE)
	    ids = regex.findall(r.text)
	    factor=[]
	    regex = re.compile("value=\"([0-9\^\-]+)\"", re.IGNORECASE)
	    for i in range(1,len(ids)):
	        fact_id=ids[i]
	        factr=s.get(url_2 % fact_id, verify=False)
	        key=regex.findall(factr.text)[0]
	        factor.append(key)
	    return factor

	npq1=crack(n1)
	p1=int(npq1[0])
	q1=int(npq1[1])
	npq2=crack(n2)
	p2=int(npq2[0])
	q2=int(npq2[1])
	d1 = inverse(e, (p1-1)*(q1-1))
	d2 = inverse(e, (p2-1)*(q2-1))
	pkey2 = RSA.construct((n2, e, d2, p2, q2))
	pkey1 = RSA.construct((n1, e, d1, p1, q1))

	m2 = pkey2.decrypt(c)
	m1 = pkey1.decrypt(m2)
	try:
	    return long_to_bytes(m1).decode('UTF-8')
	except:
	    m = long_to_bytes(m1)
	    end = m.index(0x7d)
	    return m[:end+1].decode('UTF-8')


def weinerrsa(n,e,c):
	def r2c(x,y):
		a=x//y
		pquotient=[a]
		while a*y!=x:
			x,y=y,x-a*y
			a=x//y
			pquotient.append(a)
		return pquotient
	def cfc(frac):
		convs=[];
		for i in range(len(frac)):
			convs.append(c2r(frac[0:i]))
		return convs
	def c2r(frac):
		if len(frac)==0:
			return (0,1)
		num=frac[-1]
		denom=1
		for _ in range(-2,-len(frac)-1, -1):
			num,denom= frac[_]*num+denom, num
		return(num,denom)
	def egcd(a,b):
		if a==0:
			return (b,0,1)
		g,x,y=egcd(b%a,a)
		return (g, y - (b//a)*x, x)
	def modinv(a,m):
		g,x,_=egcd(a,m)
		return (x+m)%m
	def isqrt(n):
		x=n
		y=(x+1)//2
		while y<x:
			x=y
			y=(x+n//x)//2
		return x
	def crack(e,n):
		frac=r2c(e,n)
		convergents=cfc(frac)
		for (k,d) in convergents:
			if k!=0 and (e*d-1)%k==0:
				phi=(e*d-1)//k
				s=n-phi+1
				D= s*s-4*n
				if D >=0:
					sq=isqrt(D)
					if sq*sq==D and (s+sq)%2==0: return d
	d=crack(e,n)
	m=pow(c,d,n)
	flag=repr(binascii.unhexlify(hex(m)[2:]))
	return flag[2:]
	

def commonmodulo(n,e1,e2,c1,c2):
	def egcd(a, b):
	  if (a == 0):
	    return (b, 0, 1)
	  else:
	    g, y, x = egcd(b % a, a)
	    return (g, x - (b // a) * y, y)

	# Calculates a^{b} mod n when b is negative
	def neg_pow(a, b, n):
	  assert b < 0
	  assert GCD(a, n) == 1
	  res = int(gmpy2.invert(a, n))
	  res = pow(res, b*(-1), n)
	  return res
	g, a, b = egcd(e1, e2)
	if a < 0:
	  c1 = neg_pow(c1, a, n)
	else:
	  c1 = pow(c1, a, n)
	if b < 0:
	  c2 = neg_pow(c2, b, n)
	else:
	  c2 = pow(c2, b, n)
	ct = c1*c2 % n
	m = int(gmpy2.iroot(ct, g)[0])
	return long_to_bytes(m).decode('UTF-8')		

def classicrsa(n,e,c):
	url_1='http://factordb.com/index.php?query=%i'
	url_2 ='http://factordb.com/index.php?id=%s'
	s = requests.Session()
	r = s.get(url_1 %n, verify=False)
	regex = re.compile("index\.php\?id\=([0-9]+)", re.IGNORECASE)
	ids = regex.findall(r.text)
	factor=[]
	regex = re.compile("value=\"([0-9\^\-]+)\"", re.IGNORECASE)
	for i in range(1,len(ids)):
	    fact_id=ids[i]
	    factr=s.get(url_2 % fact_id, verify=False)
	    key=regex.findall(factr.text)[0]
	    factor.append(key)
	#from here the will be passed as list and len of list will tell
	if len(factor) >2 :
		print("\033[1;32;40m","[+] Multiple Prime Factors Found.\n")
		print("\033[1;32;40m","[+] Multi Prime Attack.\n")
	phi=1
	for i in range(0,len(factor)):
	    phi=phi*(int(factor[i])-1)
	d = inverse( e, phi )
	m = pow( c, d, n )
	flag=repr(binascii.unhexlify(hex(m)[2:]))
	return flag[2:]

def crt(p,q,dp,dq,c):
	p=p
	q=q
	dp=dp
	dq=dq
	c=c
	def egcd(a, b):
	    if a == 0:
	        return (b, 0, 1)
	    else:
	        g, x, y = egcd(b % a, a)
	        return (g, y - (b // a) * x, x)

	def decryptRSA(p,q,e,ct):
	    # compute n
	    n = p * q
	    phi = (p - 1) * (q - 1) 
	    gcd, a, b = egcd(e, phi)
	    d = a
	    pt = pow(ct, d, n)
	    return pt

	def mulinv(b, n):
	    g, x, _ = egcd(b, n)
	    if g == 1:
	        return x % n
	Qinv = mulinv(q,p)
	m1 = pow(c, dp, p)
	m2 = pow(c, dq, q)
	h = (Qinv * (m1 - m2)) % p
	m = m2 + (h*q)
	flag= repr(binascii.unhexlify(hex(m)[2:]))
	return flag[2:-1]

def rot47(enc):
    decode = []
    data=enc
    for i in range(len(data)):
        encoded = ord(data[i])
        if encoded >= 33 and encoded <= 126:
            decode.append(chr(33 + ((encoded + 14) % 94)))
        else:
            decode.append(data[i])
    return ''.join(decode)

def rot(enc,key):
    dec=""
    for word in enc:
        if(word.isupper()):
            dec = dec + chr((ord(word) - key - 65) % 26 + 65)
        elif(word.islower()):
            dec = dec + chr((ord(word) - key - 97) % 26 + 97)
        else:
            dec += word
    return dec

def morse(enc):
	cipher = enc.lower()
	pool = {'.-':'a','..--.-':'_','-...':'b','-.-.':'c','-..':'d','.':'e','..-.':'f','--.':'g','....':'h','..':'i','.---':'j','-.-':'k','.-..':'l','--':'m','-.':'n','---':'o','.--.':'p','--.-':'q','.-.':'r','...':'s','-':'t','..-':'u','...-':'v','.--':'w','-..-':'x','-.--':'y','--..':'z','.----':'1','..---':'2','...--':'3','....-':'4','.....':'5','-....':'6','--...':'7','---..':'8','----.':'9','-----':'0','--..--':',','.-.-.-':'.','..--..':'?','-..-.':'/','-....-':'-','-.--.':'(','-.--.-':')','.......':' ','/': ' '}
	plain=""
	text=""
	prev=""
	for word in cipher:
		if(word != ' '):
			text += word
			prev=text	
		else:
			plain += pool[text]
			text = ""
	plain+=pool[prev]
	print("\033[1;33;40m","[+] Place { } Manually If Required")
	return plain

def dna(enc):
	cipher=enc
	#Three Character Block
	print("\033[1;33;40m","[+] Doing Standard Decoding")
	mapp={
	'AAA':'a', 'AAC':'b', 'AAG':'c', 'AAT':'d', 
	'ACA':'e', 'ACC':'f', 'ACG':'g', 'ACT':'h',
	'AGA':'i', 'AGC':'j', 'AGG':'k', 'AGT':'l',
	'ATA':'m', 'ATC':'n', 'ATG':'o', 'ATT':'p',
	'CAA':'q', 'CAC':'r', 'CAG':'s', 'CAT':'t',
	'CCA':'u', 'CCC':'v', 'CCG':'w', 'CCT':'x',
	'CGA':'y', 'CGC':'z', 'CGG':'A', 'CGT':'B',
	'CTA':'C', 'CTC':'D', 'CTG':'E', 'CTT':'F',
	'GAA':'G', 'GAC':'H', 'GAG':'I', 'GAT':'J',
	'GCA':'K', 'GCC':'L', 'GCG':'M', 'GCT':'N',
	'GGA':'O', 'GGC':'P', 'GGG':'Q', 'GGT':'R',
	'GTA':'S', 'GTC':'T', 'GTG':'U', 'GTT':'V',
	'TAA':'W', 'TAC':'X', 'TAG':'Y', 'TAT':'Z',
	'TCA':'1', 'TCC':'2', 'TCG':'3', 'TCT':'4',
	'TGA':'5', 'TGC':'6', 'TGG':'7', 'TGT':'8',
	'TTA':'9', 'TTC':'0', 'TTG':' ', 'TTT':'.',
	}
	dec=[]
	for x in range(0,len(enc),3):
		piece=enc[x:x+3]
		dec.append(mapp[piece])
	return ''.join(dec)

def brainfuck(enc):
	def evalu(code):
	  dec=''
	  code = cleanup(list(code))
	  bracemap = buildbracemap(code)
	  cell, cdp, clp = [0], 0, 0
	  while cdp < len(code):
	    command = code[cdp]
	    if command == ">":
	      clp += 1
	      if clp == len(cell): cell.append(0)
	    if command == "<":
	      clp = 0 if clp <= 0 else clp - 1
	    if command == "+":
	      cell[clp] = cell[clp] + 1 if cell[clp] < 255 else 0
	    if command == "-":
	      cell[clp] = cell[clp] - 1 if cell[clp] > 0 else 255
	    if command == "[" and cell[clp] == 0: 
	    	cdp = bracemap[cdp]
	    if command == "]" and cell[clp] != 0: 
	    	cdp = bracemap[cdp]
	    if command == ".": 
	    	dec+=chr(cell[clp])
	    if command == ",": 
	    	cell[clp] = ord(getch.getch())
	    cdp += 1
	  print("\033[1;32;40m","[+] Found:",dec)
	def cleanup(code):
	  return ''.join(filter(lambda x: x in ['.', ',', '[', ']', '<', '>', '+', '-'], code))
	def buildbracemap(code):
	  temp_bracestack, bracemap = [], {}
	  for position, command in enumerate(code):
	    if command == "[": temp_bracestack.append(position)
	    if command == "]":
	      start = temp_bracestack.pop()
	      bracemap[start] = position
	      bracemap[position] = start
	  return bracemap
	evalu(enc)


def bacon26(enc):
		lookup = {'A':'aaaaa', 'B':'aaaab', 'C':'aaaba', 'D':'aaabb', 'E':'aabaa', 
		    'F':'aabab', 'G':'aabba', 'H':'aabbb', 'I':'abaaa', 'J':'abaab', 
		    'K':'ababa', 'L':'ababb', 'M':'abbaa', 'N':'abbab', 'O':'abbba', 
		    'P':'abbbb', 'Q':'baaaa', 'R':'baaab', 'S':'baaba', 'T':'baabb', 
		    'U':'babaa', 'V':'babab', 'W':'babba', 'X':'babbb', 'Y':'bbaaa', 'Z':'bbaab'}
		decipher = '' 
		i = 0
		enc=enc.lower()
		while True : 
		    if(i < len(enc)-4): 
		        substr = enc[i:i + 5] 
		        if(substr[0] != ' '): 
		            decipher += list(lookup.keys())[list(lookup.values()).index(substr)] 
		            i += 5 
		        else: 
		            decipher += ' '
		            i += 1 
		    else: 
		        break # emulating a do-while loop 
		return decipher

def bacon24(enc):
		lookup = {'A':'aaaaa', 'B':'aaaab', 'C':'aaaba', 'D':'aaabb', 'E':'aabaa', 
		    'F':'aabab', 'G':'aabba', 'H':'aabbb', 'I':'abaaa', 'K':'abaab', 
		    'L':'ababa', 'M':'ababb', 'N':'abbaa', 'O':'abbab', 'P':'abbba', 
		    'Q':'abbbb', 'R':'baaaa', 'S':'baaab', 'T':'baaba', 'U':'baabb', 
		    'W':'babaa', 'X':'babab', 'Y':'babba', 'Z':'babbb'}
		decipher = '' 
		i = 0
		enc=enc.lower()
		while True : 
		    if(i < len(enc)-4): 
		        substr = enc[i:i + 5] 
		        if(substr[0] != ' '): 
		            decipher += list(lookup.keys())[list(lookup.values()).index(substr)] 
		            i += 5 
		        else: 
		            decipher += ' '
		            i += 1 
		    else: 
		        break # emulating a do-while loop 
		return decipher

def vignereMatrix(r,c):

	alpha ={'A':0,'B':1,'C':2,'D':3,'E':4,'F':5,'G':6,'H':7,'I':8,'J':9,'K':10,'L':11,'M':12,'N':13,'O':14,'P':15,'Q':16,'R':17,'S':18,'T':19,'U':20,'V':21,'W':22,'X':23,'Y':24,'Z':25	}

	matrix =[
	['A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M', 'N', 'O', 'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z'], 
	['B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M', 'N', 'O', 'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z', 'A'], 
	['C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M', 'N', 'O', 'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z', 'A', 'B'], 
	['D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M', 'N', 'O', 'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z', 'A', 'B', 'C'], 
	['E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M', 'N', 'O', 'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z', 'A', 'B', 'C', 'D'], 
	['F', 'G', 'H', 'I', 'J', 'K', 'L', 'M', 'N', 'O', 'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z', 'A', 'B', 'C', 'D', 'E'], 
	['G', 'H', 'I', 'J', 'K', 'L', 'M', 'N', 'O', 'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z', 'A', 'B', 'C', 'D', 'E', 'F'], 
	['H', 'I', 'J', 'K', 'L', 'M', 'N', 'O', 'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z', 'A', 'B', 'C', 'D', 'E', 'F', 'G'], 
	['I', 'J', 'K', 'L', 'M', 'N', 'O', 'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z', 'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H'], 
	['J', 'K', 'L', 'M', 'N', 'O', 'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z', 'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I'], 
	['K', 'L', 'M', 'N', 'O', 'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z', 'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J'], 
	['L', 'M', 'N', 'O', 'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z', 'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K'], 
	['M', 'N', 'O', 'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z', 'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L'], 
	['N', 'O', 'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z', 'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M'], 
	['O', 'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z', 'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M', 'N'], 
	['P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z', 'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M', 'N', 'O'], 
	['Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z', 'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M', 'N', 'O', 'P'], 
	['R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z', 'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M', 'N', 'O', 'P', 'Q'], 
	['S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z', 'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M', 'N', 'O', 'P', 'Q', 'R'], 
	['T', 'U', 'V', 'W', 'X', 'Y', 'Z', 'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M', 'N', 'O', 'P', 'Q', 'R', 'S'], 
	['U', 'V', 'W', 'X', 'Y', 'Z', 'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M', 'N', 'O', 'P', 'Q', 'R', 'S', 'T'], 
	['V', 'W', 'X', 'Y', 'Z', 'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M', 'N', 'O', 'P', 'Q', 'R', 'S', 'T', 'U'], 
	['W', 'X', 'Y', 'Z', 'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M', 'N', 'O', 'P', 'Q', 'R', 'S', 'T', 'U', 'V'], 
	['X', 'Y', 'Z', 'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M', 'N', 'O', 'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W'], 
	['Y', 'Z', 'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M', 'N', 'O', 'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X'], 
	['Z', 'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M', 'N', 'O', 'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y']]

	row = alpha[r]
	i=0
	while(i<26):
		if(matrix[row][i]==c):
			col=i
			break;
		i+=1

	return(matrix[0][col])


def vigenere(enc,key):
	def new_alph(ch):
	    ch = ch.lower()
	    alph = 'abcdefghijklmnopqrstuvwxyz'
	    new_alph = alph[alph.index(ch):] + alph[:alph.index(ch)]
	    return new_alph
	def encrypt(text, big_key):
	    res = ''
	    alph = 'abcdefghijklmnopqrstuvwxyz'
	    i = 1
	    for char in big_key:
	        new = new_alph(char)
	        for t in text:
	            if alph.count(t) == 1 :
	                res += new[alph.index(t)]
	                text = text[i:]
	                break
	            elif alph.count(t.lower()) == 1:
	                res += new[alph.index(t.lower())].upper()
	                text = text[i:]
	                break
	            else:
	                res += t
	                text = text[i:]
	                break
	            i += 1    
	    return res
	def decrypt(text, big_key):
	    res = ''
	    alph = 'abcdefghijklmnopqrstuvwxyz'
	    i = 1
	    for char in big_key:
	        new = new_alph(char)
	        for t in text:
	            if alph.count(t) == 1 :
	                res += alph[new.index(t)]
	                text = text[i:]
	                break
	            elif alph.count(t.lower()) == 1:
	                res += alph[new.index(t.lower())].upper()
	                text = text[i:]
	                break
	            else:
	                res += t
	                text = text[i:]
	                break
	            i += 1    
	    return res    
	text_dec = enc
	key = key
	if len(key) <= len(text_dec):
	    big_key = key * (len(text_dec) // len(key)) + key[:len(text_dec) % len(key)]
	    text_decrypt = decrypt(text_dec, big_key)
	    return text_decrypt

def xorr(key,cipher):
	output=''
	q=len(cipher)
	for i in range(q):
		c=cipher[i]
		a=key[i%len(key)]
		output+=chr(ord(c)^ord(a))
	return output	

def vtd(cipher,key):
	def decrypt(message, keyword):
	  matrix = new1(ordering(keyword), message)

	  plaintext = "";
	  for r in range(len(matrix)):
	    for c in range (len(matrix[r])):
	      plaintext += matrix[r][c]
	  return plaintext


	def new1(keySeq, message):
	  width = len(keySeq)
	  height = math.ceil(len(message) / width)
	  if height * width < len(message):
	    height += 1

	  matrix = new2(width, height, len(message))

	  pos = 0
	  for num in range(len(keySeq)):
	    column = keySeq.index(num+1)

	    r = 0
	    while (r < len(matrix)) and (len(matrix[r]) > column):
	      matrix[r][column] = message[pos]
	      r += 1
	      pos += 1

	  return matrix


	def new2(width, height, length):
	  matrix = []
	  totalAdded = 0
	  for r in range(height):
	    matrix.append([])
	    for c in range(width):
	      if totalAdded >= length:
	        return matrix
	      matrix[r].append('')
	      totalAdded += 1
	  return matrix


	def ordering(keyword):
	  sequence = []
	  for pos, ch in enumerate(keyword):
	    previousLetters = keyword[:pos]
	    newNumber = 1
	    for previousPos, previousCh in enumerate(previousLetters):
	      if previousCh > ch:
	        sequence[previousPos] += 1
	      else:
	        newNumber += 1
	    sequence.append(newNumber)
	  return sequence

	dec = decrypt(cipher,key)
	return dec	


def crypto():	
	os.system('clear')
	banner()
	print('\033[1;33;40m[+]')
	print('\033[1;33;40m [=> Crypto Module Loaded\n')
	print('\033[1;33;40m [1] Base(32,64,85) Decoder ')
	print('\033[1;33;40m [2] Number System(Binary, Octal, Decimal, Haxadecimal) Decoder ')
	print('\033[1;33;40m [3] Rot(n,47) Decoder ')
	print('\033[1;33;40m [4] Morse Decoder ')
	print('\033[1;33;40m [5] RSA(Classic, Cube Root, Common Modulus, Wiener Attack, Chinese Remainder, Twin Prime) Decoder ')
	print('\033[1;33;40m [6] DNA Decoder ')
	print('\033[1;33;40m [7] BrainF#ck Decoder ')
	print('\033[1;33;40m [8] Bacon Decoder ')
	print('\033[1;33;40m [9] Vigenere Decoder ')
	print('\033[1;33;40m [10] XOR Decoder ')
	print('\033[1;33;40m [11] Vertical Transposition Decoder ')

	choice2=int(input('\n>'))
	if choice2 == 1:
		os.system('clear')
		banner()
		print('\033[1;33;40m [=> Base Decoder ')
		print('\033[1;33;40m [1] Base32 Decoder ')
		print('\033[1;33;40m [2] Base64 Decoder ')
		print('\033[1;33;40m [3] Base85 Decoder ')
		choice3=int(input('\n>'))
		if choice3 == 1:
			cipher=input('\033[1;33;40m[>] Give Cipher: ')
			print("\033[1;32;40m[+][+]Found:",b32(cipher),'\n')
			time.sleep(2)
			status=int(input(('\033[1;33;40mPress 0 To Get Back To Crypto Menu OR Ctrl+c ')))
			if status==0:
				crypto()
		elif choice3==2:
			cipher=input('\033[1;33;40m[>] Give Cipher: ')
			print("\033[1;32;40m[+][+]Found:",b64(cipher),'\n')
			time.sleep(2)
			status=int(input(('\033[1;33;40mPress 0 To Get Back To Crypto Menu OR Ctrl+c ')))
			if status==0:
				crypto()
		elif choice3==3:
			cipher=input('\033[1;33;40m[>] Give Cipher: ')
			print("\033[1;32;40m[+][+]Found:",b85(cipher),'\n')
			time.sleep(2)
			status=int(input(('\033[1;33;40mPress 0 To Get Back To Crypto Menu OR Ctrl+c ')))
			if status==0:
				crypto()
		else:
			print("\033[1;31;40mWrong Option !!\n")


	elif choice2==2:
		os.system('clear')
		banner()
		print('\033[1;33;40m [=> Number Decoder ')
		print('\033[1;33;40m [1] Binary Decoder ')
		print('\033[1;33;40m [2] Octal Decoder ')
		print('\033[1;33;40m [3] Decimal Decoder ')
		print('\033[1;33;40m [4] Hex Decoder ')
		choice3=int(input('\n>'))
		if choice3 == 1:
			cipher=input('\033[1;33;40m[>] Give Cipher: ')
			print("\033[1;32;40m[+][+]Found:",bintotext(cipher),'\n')
			time.sleep(2)
			status=int(input(('\033[1;33;40mPress 0 To Get Back To Crypto Menu OR Ctrl+c ')))
			if status==0:
				crypto()
		elif choice3==2:
			cipher=input('\033[1;33;40m[>] Give Cipher: ')
			print("\033[1;32;40m[+][+]Found:",octtotext(cipher),'\n')
			time.sleep(2)
			status=int(input(('\033[1;33;40mPress 0 To Get Back To Crypto Menu OR Ctrl+c ')))
			if status==0:
				crypto()
		elif choice3==3:
			cipher=input('\033[1;33;40m[>] Give Cipher: ')
			print("\033[1;32;40m[+][+]Found:",dectotext(cipher),'\n')
			time.sleep(2)
			status=int(input(('\033[1;33;40mPress 0 To Get Back To Crypto Menu OR Ctrl+c ')))
			if status==0:
				crypto()
		elif choice3==4:
			cipher=input('\033[1;33;40m[>] Give Cipher: ')
			print("\033[1;32;40m[+][+]Found:",hextotext(cipher),'\n')
			time.sleep(2)
			status=int(input(('\033[1;33;40mPress 0 To Get Back To Crypto Menu OR Ctrl+c ')))
			if status==0:
				crypto()	
		else:
			print("\033[1;31;40mWrong Option !!\n")		

	elif choice2 == 3:
		os.system('clear')
		banner()
		print('\033[1;33;40m [=> Rot Decoder ')
		print('\033[1;33;40m [1] Rot(N) Decoder ')
		print('\033[1;33;40m [2] Rot47 Decoder ')
		choice3=int(input('\n>'))
		if choice3 == 1:
			cipher=input('\033[1;33;40m[>] Give Cipher: ')
			for key in range(1,27):
				print("\033[1;32;40m[+][+]Found:",rot(cipher,key))
			time.sleep(2)
			status=int(input(('\033[1;33;40mPress 0 To Get Back To Crypto Menu OR Ctrl+c ')))
			if status==0:
				crypto()
		elif choice3==2:
			cipher=input('\033[1;33;40m[>] Give Cipher: ')
			print("\033[1;32;40m[+][+]Found:",rot47(cipher),'\n')
			time.sleep(2)
			status=int(input(('\033[1;33;40mPress 0 To Get Back To Crypto Menu OR Ctrl+c ')))
			if status==0:
				crypto()
		else:
			print("\033[1;31;40mWrong Option !!\n")		

	elif choice2 == 4:
		os.system('clear')
		banner()
		print('\033[1;33;40m [=> Morse Decoder ')
		cipher=input('\033[1;33;40m[>] Give Cipher: ')
		print("\033[1;32;40m[+][+]Found:",morse(cipher),'\n')
		time.sleep(2)
		status=int(input(('\033[1;33;40mPress 0 To Get Back To Crypto Menu OR Ctrl+c ')))
		if status==0:
			crypto()

	elif choice2 == 5:
		os.system('clear')
		banner()
		print('\033[1;33;40m [=> RSA Decoder ')
		print('\033[1;33;40m [1] Classic Attack ')
		print('\033[1;33;40m [2] Cube Root Attack ')
		print('\033[1;33;40m [3] Common Modulo Attack ')
		print('\033[1;33;40m [4] Weiner Attack ')
		print('\033[1;33;40m [5] Chinese Remainder Attack(p,q,dp,dq,c)')
		print('\033[1;33;40m [6] Twin Prime Attack(n1,n2,c,e)')
		choice3=int(input('\n>'))
		if choice3 == 1:
			cipher1=int(input('\033[1;33;40m[>] Give N: '))
			cipher2=int(input('\033[1;33;40m[>] Give E: '))
			cipher3=int(input('\033[1;33;40m[>] Give C: '))
			print("\033[1;32;40m[+][+]Found:",classicrsa(cipher1,cipher2,cipher3),'\n')
			time.sleep(2)
			status=int(input(('\033[1;33;40mPress 0 To Get Back To Crypto Menu OR Ctrl+c ')))
			if status==0:
				crypto()
		elif choice3==2:
			cipher1=int(input('\033[1;33;40m[>] Give N: '))
			cipher2=int(input('\033[1;33;40m[>] Give E: '))
			cipher3=int(input('\033[1;33;40m[>] Give C: '))
			print("\033[1;32;40m[+][+]Found:",cuberootrsa(cipher1,cipher2,cipher3),'\n')
			time.sleep(2)
			status=int(input(('\033[1;33;40mPress 0 To Get Back To Crypto Menu OR Ctrl+c ')))
			if status==0:
				crypto()
		elif choice3==3:
			n=int(input('\033[1;33;40m[>] Give n: '))
			e1=int(input('\033[1;33;40m[>] Give e1: '))
			e2=int(input('\033[1;33;40m[>] Give e2: '))
			c1=int(input('\033[1;33;40m[>] Give c1: '))
			c2=int(input('\033[1;33;40m[>] Give c2: '))
			print("\033[1;32;40m[+][+]Found:",commonmodulo(n,e1,e2,c1,c2),'\n')
			time.sleep(2)
			status=int(input(('\033[1;33;40mPress 0 To Get Back To Crypto Menu OR Ctrl+c ')))
			if status==0:
				crypto()
		elif choice3==4:
			cipher1=int(input('\033[1;33;40m[>] Give N: '))
			cipher2=int(input('\033[1;33;40m[>] Give E: '))
			cipher3=int(input('\033[1;33;40m[>] Give C: '))
			print("\033[1;32;40m[+][+]Found:",weinerrsa(cipher1,cipher2,cipher3),'\n')
			time.sleep(2)
			status=int(input(('\033[1;33;40mPress 0 To Get Back To Crypto Menu OR Ctrl+c ')))
			if status==0:
				crypto()
		elif choice3==5:
			cipher1=int(input('\033[1;33;40m[>] Give p: '))
			cipher2=int(input('\033[1;33;40m[>] Give q: '))
			cipher3=int(input('\033[1;33;40m[>] Give dp: '))
			cipher4=int(input('\033[1;33;40m[>] Give dq: '))
			cipher5=int(input('\033[1;33;40m[>] Give c: '))
			print("\033[1;32;40m[+][+]Found:",crt(cipher1,cipher2,cipher3,cipher4,cipher5),'\n')
			time.sleep(2)
			status=int(input(('\033[1;33;40mPress 0 To Get Back To Crypto Menu OR Ctrl+c ')))
			if status==0:
				crypto()
		elif choice3==6:
			cipher1=int(input('\033[1;33;40m[>] Give n1: '))
			cipher2=int(input('\033[1;33;40m[>] Give n2: '))
			cipher3=int(input('\033[1;33;40m[>] Give c: '))
			cipher4=int(input('\033[1;33;40m[>] Give e: '))
			print("\033[1;32;40m[+][+]Found:",twinprime(cipher1,cipher2,cipher3,cipher4),'\n')
			time.sleep(2)
			status=int(input(('\033[1;33;40mPress 0 To Get Back To Crypto Menu OR Ctrl+c ')))
			if status==0:
				crypto()
								
		else:
			print("\033[1;31;40mWrong Option !!\n")		

	elif choice2==6:
		os.system('clear')
		banner()
		print('\033[1;33;40m [=> DNA Decoder ')
		cipher=input('\033[1;33;40m[>] Give Cipher: ')
		print("\033[1;32;40m[+][+]Found:",dna(cipher),'\n')
		time.sleep(2)
		status=int(input(('\033[1;33;40mPress 0 To Get Back To Crypto Menu OR Ctrl+c ')))
		if status==0:
			crypto()

	elif choice2==7:
		os.system('clear')
		banner()
		print('\033[1;33;40m [=> brainf#ck Decoder ')
		cipher=input('\033[1;33;40m[>] Give Cipher: ')
		brainfuck(cipher)
		time.sleep(2)
		status=int(input(('\033[1;33;40mPress 0 To Get Back To Crypto Menu OR Ctrl+c ')))
		if status==0:
			crypto()

	elif choice2==8:
		os.system('clear')
		banner()
		print('\033[1;33;40m [=> Bacon Decoder ')
		cipher=input('\033[1;33;40m[>] Give Cipher: ')
		print("\033[1;32;40m[+][+]Found(26 Letter Bacon):",bacon26(cipher),'\n')
		print("\033[1;32;40m[+][+]Found(24 Letter Bacon):",bacon24(cipher),'\n')
		time.sleep(2)
		status=int(input(('\033[1;33;40mPress 0 To Get Back To Crypto Menu OR Ctrl+c ')))
		if status==0:
			crypto()

	elif choice2==9:
		os.system('clear')
		banner()
		print('\033[1;33;40m [=> Vignere Decoder ')
		cipher=input('\033[1;33;40m[>] Cipher: ')
		key=input('\033[1;33;40m[>] Key: ')
		print("\033[1;32;40m[+][+]Found:",vigenere(cipher,key),'\n')
		time.sleep(2)
		status=int(input(('\033[1;33;40mPress 0 To Get Back To Crypto Menu OR Ctrl+c ')))
		if status==0:
			crypto()		
		
	elif choice2==10:
		os.system('clear')
		banner()
		print('\033[1;33;40m [=> XOR Decoder ')
		cipher=input('\033[1;33;40m[>] Cipher: ')
		key=input('\033[1;33;40m[>] Key: ')
		print("\033[1;32;40m[+][+]Found:",xorr(key,cipher),'\n')

	elif choice2==11:
		os.system('clear')
		banner()
		print('\033[1;33;40m [=> Vertical Transposition Decoder ')
		cipher=input('\033[1;33;40m[>] Cipher: ')
		key=input('\033[1;33;40m[>] Key: ')
		print("\033[1;32;40m[+][+]Found:",vtd(cipher,key),'\n')

	else:
		print("\033[1;31;40mWrong Option !!\n")

#BANNNER
def banner():
	banner1 = Figlet(font='bulbhead')
	print(colored.green(banner1.renderText("     DAGGER")))
	banner2 = Figlet(font='digital')
	print(colored.yellow(banner2.renderText(" |||Your Crypto Assistant|||")))
try:
	os.system('clear')
	banner()
	print("\033[1;33;40m 	     May The Flag Be With You")
	time.sleep(1)
	crypto()
except KeyboardInterrupt :
	sys.exit(0)	
