Add LoadPath "/Users/mzp/Downloads/applpi".
Require libapplpi.
Add LoadPath "/Users/mzp/Downloads/applpi/mail-server".
Load "SMTP_applpi_string.v".
Load "SMTP_applpi_Exceptions.v".
Load "SMTP_FileSystem.v".
Require PolyList.
Load "SMTP_applpi_Rfc821.v".
Load "SMTP_applpi.v".
Load "SMTP_applpi_spec.v".
Require Classical.
Require JMeq.
Require Arith.

Extract Inlined Constant String => "string".
Extract Constant server_name0 => """server_name""".
Extract Inlined Constant File => string.
Extract Constant queue_dir0 => """/queue_dir""".
Extract Inlined Constant Buffer => string.
Extract Constant buf0 => """/buf""".
Extract Inlined Constant Rfc821_path => string.
Extract Constant from_domain0 => """""". null string
Extract Constant rev_path0 => """""". null string

Extract Constant is_nullstr => "fun s -> if String.length s = 0 then true else false".
Extract Constant IOexn_chan => "new channel".
Extract Constant result_chan => "new channel".

Extract Constant parseRfc821path => "fun s -> (SUCC (s, ()))".
Extract Constant is_not_null_a_d_l => "fun s -> if String.length s = 0 then false else true".
Extract Inlined Constant OutputStream => "replyMsg channel".
Extract Inlined Constant InputStream => "sMTP_cmd channel".
Extract Inlined Constant ToFileSystem => "mail channel".

Extract Inductive bool => bool [true false].
Extract Inductive unit => unit [ "()" ].

Recursive Extraction work.
