val _ = Control.Print.printDepth := 10;
val _ = Control.Print.printLength := 10;
val _ = Control.Print.stringDepth := 2000;
val _ = Control.polyEqWarn := false;

(* usefull for making unit tests *)
fun readFile filename =
  let val is = TextIO.openIn filename
  in 
    String.map (fn c => if Char.isGraph c orelse c = #" " orelse c = #"\n" then c else #" ")
      (TextIO.inputAll is)
    before TextIO.closeIn is
  end

(* exception for non-implemented functions *)
exception NotImplemented;

signature RING =
    sig
        eqtype t
        val zero : t
        val one : t
        val neg : t -> t
        val xGCD : t * t -> t * t * t
        val inv : t -> t option
        val + : t * t -> t
        val * : t * t -> t
    end

signature MAT =
    sig
        eqtype t
        structure Vec :
            sig
            val dot : t list -> t list -> t
            val add : t list -> t list -> t list
            val sub : t list -> t list -> t list
            val scale : t -> t list -> t list
            end
        val tr : t list list -> t list list
        val mul : t list list -> t list list -> t list list
        val id : int -> t list list
        val join : t list list -> t list list -> t list list
        val inv : t list list -> t list list option
    end


signature CIPHER =
    sig
        type t
        val encrypt : t list list -> t list -> t list
        val decrypt : t list list -> t list -> t list option
        val knownPlaintextAttack : int -> t list -> t list -> t list list option
    end

fun xGCD (n1, n2) =
   if n2 = 0 then
       (n1, 1, 0)
   else
       let
           val (u, s, t) = xGCD(n2, n1 mod n2)
       in
           (u, t, s - (n1 div n2) * t)
       end

structure Trie :> 
sig
eqtype ''a dict
val empty : ''a dict
val insert : ''a list -> ''a dict -> ''a dict
val lookup : ''a list -> ''a dict -> bool
end
=
struct
  datatype ''a tree = N of ''a * bool * ''a tree list
  type ''a dict = ''a tree list

  val empty = [] : ''a dict

  fun insert w dict = raise NotImplemented
  fun lookup w dict = raise NotImplemented
end;


functor Ring (val n : int) :> RING where type t = int =
    struct
        type t = int
        val zero = 0
        val one = 1
        fun neg x = ~x mod n

        val xGCD = xGCD
 
    
        fun inv x =
            case xGCD(x mod n, n) of
            (1, s, _) => SOME (s mod n)
            | _ => NONE

        fun op + a =  Int.+ a mod n
        fun op * p =  Int.* p mod n
    end

functor Mat (R : RING) :> MAT where type t = R.t =
    struct
        type t = R.t

        structure Vec = 
            struct
                fun add a b =
                    case (a,b) of
                        ([], []) => []
                        | (x::xs, y::ys) => R.+(x, y)::add xs ys
                        | (_,_) => raise Fail "Vector lengths do not match"

                fun sub a b = 
                    case (a,b) of
                        ([], []) => []
                        | (x::xs, y::ys) => (R.+(x,R.neg(y)))::sub xs ys
                        |(_,_) => raise Fail "Vector lengths do not match"
                
                fun scale n ls =
                    case ls of
                        [] => []
                        | x::xs => R.*(n,x)::scale n xs
                
                fun dot a b = 
                    case (a,b) of
                        ([], []) => R.zero
                        |(x::xs, y::ys) => R.+(R.*(x,y), dot xs ys)
                        |(_,_) => raise Fail "Vector lengths do not match"
            end

        fun getNthColumn(n : int, matr : t list list) : t list = 
            case matr of
                [] => []
                | r::rs => 
                            let
                                fun getNthElement(0, row) = hd row
                                    | getNthElement(i, f::fs) = getNthElement(i - 1, fs)
                                    | getNthElement(_, _) = raise Fail "Index out of bound exception"
                            in
                                getNthElement(n, r)::getNthColumn(n, rs)
                            end

        fun tr mat= 
            let                        
                fun getNoOfColumns(randomRowInMatrix : t list) : int =
                    case randomRowInMatrix of
                        [] => 0
                        | _ => 1 + getNoOfColumns(tl randomRowInMatrix)
                
                fun getAllColumns(columnIx : int, noOfColumns : int, mtr : t list list) : t list list = 
                    if columnIx = noOfColumns then [] 
                    else getNthColumn(columnIx, mtr)::getAllColumns(columnIx+1, noOfColumns, mtr)
            in

                if null mat then [] else getAllColumns(0, getNoOfColumns(hd mat), mat)
            end


        fun mul mat1 mat2 =
            let
                val transposedMat2 = tr mat2;

                fun multiplyRow(row: t list): t list =
                    map (fn col => Vec.dot row col) transposedMat2
            in
                map multiplyRow mat1
            end

                
        fun join mat1 mat2 = 
            case (mat1,mat2) of
                ([], _) => mat2
                | (_, []) => mat1
                | (_,_) =>
                        if length mat1 = length mat2 then
                            ListPair.map (fn (row1, row2) => row1 @ row2) (mat1, mat2)
                        else
                            raise Fail "Matrices lengths do not match"
         
         
        fun id n =
            let
                fun row(i : int) =
                    List.tabulate (n, fn j => if i = j then R.one else R.zero)
            in
                List.tabulate (n, row)
            end


        fun reduce v m = 
            List.map (fn u :: us => 
                Vec.sub us (Vec.scale u v) 
                | _ => raise NotImplemented) m;

        fun pivot(z, mt) = 
            case (z, mt) of
                ([], _) => NONE
                | (v as x::xs, mat) => let
                                        val xInv = R.inv x
                                    in
                                        case xInv of
                                            SOME x' => SOME ((Vec.scale x' v)::mat)
                                            | NONE =>
                                                case mat of
                                                    [] => NONE
                                                    | (u as y::ys)::matr => let
                                                                                val (_, s, t) = R.xGCD (x, y)
                                                                            in
                                                                             case pivot (Vec.add (Vec.scale s v) (Vec.scale t u), matr) of
                                                                                SOME (w :: matrix) => SOME (w :: v :: u :: matrix)
                                                                                | _ => NONE
                                                                            end
                                            |_ => NONE
                                    end


        fun gauss (u, b) = 
            case (u, b) of
                (sth, []) => SOME sth
                |(sth,b::bs) =>  let
                                    val p = pivot (b, bs)
                                in
                                    case p of
                                        NONE => NONE
                                        | SOME ((_ :: b') :: bs') => 
                                            gauss (reduce b' u @ [b'], List.filter (fn x => not (List.all (fn y => y = R.zero) x)) (reduce b' bs'))
                                        | SOME whatever => NONE
                                end


        fun inv mat = 
            if List.length mat > 0 then gauss([], (join (mat) (id (List.length mat))))
            else gauss([], (join (mat) (id 0)))


end

fun takeN([], _) = []
  | takeN(_, 0) = []
  | takeN(x::xs, n) = if n > length (x::xs) then [] else x :: takeN(xs, n - 1)

fun dropN([], _) = []
  | dropN(lst, 0) = lst
  | dropN(x::xs, n) = if n > length (x::xs) then [] else dropN(xs, n - 1)


fun split blockSize lst =
    let
        fun splitRec([], acc) = rev acc
          | splitRec(xs, acc) =
            let
                val (block, rest) = (takeN(xs, blockSize), dropN(xs, blockSize))
            in
                if blockSize > length xs then splitRec([], acc)
                else splitRec(rest, block :: acc)
            end
    in
        splitRec(lst, [])
    end


functor HillCipherAnalyzer (M : MAT) :> CIPHER where type t = M.t =
    struct
        type t = M.t

        fun encrypt key plaintext = 
            let
                val length = length key
                val blocks = split length plaintext

                val encryptedMatrix = M.mul blocks key

                val encryptedPlainText = List.concat encryptedMatrix
            in
                encryptedPlainText
            end


        fun decrypt key ciphertext =
            let
                val invKey = M.inv key
                
            in
                case invKey of
                    SOME ik => let
                                    val length = length ik

                                    val encBlocks = split length ciphertext

                                    val decryptedMatrix = M.mul encBlocks ik

                                    val decryptedPlainText = List.concat decryptedMatrix

                                in
                                  SOME decryptedPlainText  
                                end
                    | NONE => NONE
            end

        fun areMatricesEqual(matrix1, matrix2) =
            let

                fun areListsEqual([], []) = true
                    | areListsEqual(x::xs, y::ys) = (x = y) andalso areListsEqual(xs, ys)
                    | areListsEqual _ = false

                fun areRowsEqual([], []) = true
                | areRowsEqual(row1::rows1, row2::rows2) =
                    (areListsEqual(row1, row2)) andalso areRowsEqual(rows1, rows2)
                | areRowsEqual _ = false
            in
                areRowsEqual(matrix1, matrix2)
            end


        fun knownPlaintextAttack keyLength plaintext ciphertext = 
            let
                val blocksPlainText = split keyLength plaintext
                val blocksCipherText = split keyLength ciphertext

                val plaintextFirstT = if List.length blocksPlainText < keyLength then [] else List.take(blocksPlainText, keyLength)
                val cipherTextFirstT = if List.length blocksCipherText < keyLength then [] else List.take(blocksCipherText, keyLength)
 
                val invPlainTextFirstT = M.inv plaintextFirstT

                val plaintextTplusOne = plaintextFirstT
                val blocksCipherTextTPlusOne = cipherTextFirstT


                fun addRowToMatrix(originalmatrix : t list list, 
                    newMatrix : t list list, 
                    rowIx : int) : t list list = 

                    if length originalmatrix <= rowIx then []
                    else 
                        let
                            val rowToAdd = List.nth(originalmatrix, rowIx)
                        in
                            newMatrix @ [rowToAdd]
                        end


                fun plaintextAttackHelper(currentRowIx : int, plaintextTPlusOne : t list list, 
                    blocksCipherTextTPlusOne : t list list, 
                    plainTextOriginal : t list list, 
                    blocksCipherOriginal : t list list) : t list list option =
                    let
                        val nextRowIx = currentRowIx + 1
                        val xt = M.tr plaintextTPlusOne
                        val xtx = M.mul xt plaintextTPlusOne
                        val xtxInv = M.inv xtx

                        val tplusOnePlain = addRowToMatrix(plainTextOriginal, plaintextTPlusOne, nextRowIx)
                        val tplusOneCipher = addRowToMatrix(blocksCipherOriginal, blocksCipherTextTPlusOne, nextRowIx)
                    in
                        case xtxInv of
                            NONE => if null tplusOnePlain orelse null tplusOneCipher then NONE else plaintextAttackHelper(nextRowIx, tplusOnePlain, tplusOneCipher, plainTextOriginal, blocksCipherOriginal)
                            | SOME xtxInverse => let
                                                    val possibleKey = M.mul xtxInverse (M.mul xt blocksCipherTextTPlusOne)
                                                    val multipliedKeyWithplaintext = M.mul blocksPlainText possibleKey
                                                    val ciphertextsEqual = areMatricesEqual(multipliedKeyWithplaintext, blocksCipherText)
                                                 in
                                                    if ciphertextsEqual then SOME possibleKey else NONE
                                                 end
                    end
            in
                if null plaintextFirstT orelse null cipherTextFirstT then NONE 
                else
                    case invPlainTextFirstT of
                        NONE => plaintextAttackHelper(keyLength, 
                                    addRowToMatrix(blocksPlainText, plaintextTplusOne, keyLength), 
                                    addRowToMatrix(blocksCipherText, blocksCipherTextTPlusOne, keyLength), 
                                    blocksPlainText, blocksCipherText)
                        | SOME iptft => let
                                            val possibleKey = (M.mul iptft cipherTextFirstT)
                                            val multipliedKeyWithplaintext = M.mul blocksPlainText possibleKey
                                            val ciphertextsEqual = areMatricesEqual(multipliedKeyWithplaintext, blocksCipherText)
                                        in
                                            case ciphertextsEqual of
                                                false => NONE
                                                | true => SOME possibleKey
                                        end
            end
    end

signature HILLCIPHER =
sig
  structure Ring : RING where type t = int
  structure Matrix : MAT where type t = Ring.t
  structure Cipher : CIPHER where type t = Matrix.t
  val alphabetSize : int
  val alphabet : char list
  val encode : string -> Cipher.t list
  val decode : Cipher.t list -> string
  val encrypt : Cipher.t list list -> string -> string
  val decrypt : Cipher.t list list -> string -> string option
  val knownPlaintextAttack :
      int -> string -> string -> Cipher.t list list option
  val ciphertextOnlyAttack : int -> string -> Cipher.t list list option
end

functor HillCipher (val alphabet : string) :> HILLCIPHER =
struct
val alphabetSize = String.size alphabet
val alphabet = String.explode alphabet

structure Ring = Ring (val n = alphabetSize)
structure Matrix = Mat (Ring)
structure Cipher = HillCipherAnalyzer (Matrix)

fun encode txt = let
        fun findIndexHelper (c, index, []) = raise NotImplemented
          | findIndexHelper (c, index, x::xs) =
            if Char.ord c = Char.ord x then SOME index
            else findIndexHelper (c, index + 1, xs)

        fun processString ([], _) = []
            | processString (c::cs, index) =
            case findIndexHelper (c, 0, alphabet) of
                NONE => []
                | SOME i => i::processString (cs, index)
        
        val ps = processString(explode txt, 0)

        in
            if null (explode txt) then [] 
            else if null ps then raise NotImplemented else ps
        end

fun decode code = let
            fun findLetterHelper (c, index, []) = raise NotImplemented
            | findLetterHelper (c, index, x::xs) =
                if c = index then SOME x
                else findLetterHelper (c, index + 1, xs)

            fun processString ([], _) = []
            | processString (c::cs, index) =
                case findLetterHelper (c, 0, alphabet) of
                    NONE => []
                | SOME l => l::processString (cs, index)
            
            val ps = processString(code, 0)

            in
                if null code then ""
                else if null ps then raise NotImplemented else implode ps
            end

local
fun parseWords filename =
  let val is = TextIO.openIn filename
    fun read_lines is =
      case TextIO.inputLine is of
        SOME line =>
          if String.size line > 1
          then String.tokens (not o Char.isAlpha) line @ read_lines is
          else read_lines is
        | NONE => []
  in List.map (String.map Char.toLower) (read_lines is) before TextIO.closeIn is end

   val dictionary = List.foldl (fn (w, d) => Trie.insert w d) Trie.empty (List.map String.explode (parseWords "hamlet.txt")) handle NotImplemented => Trie.empty
in
  fun encrypt key plaintext = 
        let
            val encodedText = encode plaintext
            val encryptedWithKey = Cipher.encrypt key encodedText
            val decodedEncrypted = decode encryptedWithKey
        in
            decodedEncrypted
        end



  fun decrypt key ciphertext = 
        let
            val encodedCipher = encode ciphertext
            val decryptedEncoded = Cipher.decrypt key encodedCipher
            
        in
            case decryptedEncoded of
                NONE => NONE
                | SOME de => SOME (decode de)
        end


  fun knownPlaintextAttack keyLenght plaintext ciphertext = raise NotImplemented
  fun ciphertextOnlyAttack keyLenght ciphertext = raise NotImplemented
  end
end;



(*val vec1 = [1,2,4]
val vec2 = [42,~33,1]
val vec3 = [1,1,1]
structure M = Mat (Ring (val n = 27))
structure C = HillCipherAnalyzer (Mat (Ring (val n = 10)))

val key = [[1,0,0],[0,3,0],[0,0,1]]

structure M = Mat(Ring (val n = 10))
structure C = HillCipherAnalyzer (M);


(*val keyLength = 1
val plaintext = [1,2,3]
val ciphertext = [2,4,8]

                val blocksPlainText = split keyLength plaintext
                val blocksCipherText = split keyLength ciphertext

                val plaintextFirstT = if List.length blocksPlainText < keyLength then [] else List.take(blocksPlainText, keyLength)
                val cipherTextFirstT = if List.length blocksCipherText < keyLength then [] else List.take(blocksCipherText, keyLength)

                val invPlainTextFirstT = M.inv plaintextFirstT

                val plaintextTplusOne = plaintextFirstT
                val blocksCipherTextTPlusOne = cipherTextFirstT*)*)