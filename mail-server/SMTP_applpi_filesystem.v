Require Import SMTP_applpi_string.

Axiom FileSystem : Set.
Axiom FileOutputStream : Set.
Axiom FileContents : Set.
Axiom empty_file : FileContents.

Axiom File : Set. (* absolute file name *)
Axiom file_contents : File -> FileSystem -> option FileContents.
Axiom str_to_filecontents : String -> FileContents.
Axiom abs_filename : String * String -> File.
