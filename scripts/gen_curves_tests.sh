#/*
# *  Copyright (C) 2017 - This file is part of libecc project
# *
# *  Authors:
# *      Ryad BENADJILA <ryadbenadjila@gmail.com>
# *      Arnaud EBALARD <arnaud.ebalard@ssi.gouv.fr>
# *      Jean-Pierre FLORI <jean-pierre.flori@ssi.gouv.fr>
# *
# *  Contributors:
# *      Nicolas VIVET <nicolas.vivet@ssi.gouv.fr>
# *      Karim KHALFALLAH <karim.khalfallah@ssi.gouv.fr>
# *
# *  This software is licensed under a dual BSD and GPL v2 license.
# *  See LICENSE file at the root folder of the project.
# */
#!/bin/sh

# Find a suitable python command if none has been provided
if [ -z "$PYTHON" ]
then
	echo "Looking for suitable python and deps"
	# Try to guess which python we want to use depending on the installed
	# packages. We need Pyscard, Crypto, and IntelHex
	for i in python python3 python2; do
		if [ -x "`which $i`" ]; then
			echo "Found and using python=$i"
			PYTHON=$i
			break
		fi
	done
else
	echo "Using user provided python=$PYTHON"
fi

# Get the expand_libecc python script path
BASEDIR=$(dirname "$0")
EXPAND_LIBECC=$BASEDIR/expand_libecc.py

# SECP192R1
echo "SECP192R1"
$PYTHON $EXPAND_LIBECC --name="SECP192R1" --prime=6277101735386680763835789423207666416083908700390324961279 --a=6277101735386680763835789423207666416083908700390324961276 --b=2455155546008943817740293915197451784769108058161191238065 --gx=602046282375688656758213480587526111916698976636884684818 --gy=174050332293622031404857552280219410364023488927386650641 --order=6277101735386680763835789423176059013767194773182842284081 --cofactor=1 --add-test-vectors=2

# SECP224R1
echo "SECP224R1"
$PYTHON $EXPAND_LIBECC --name="SECP224R1" --prime=26959946667150639794667015087019630673557916260026308143510066298881 --a=26959946667150639794667015087019630673557916260026308143510066298878 --b=18958286285566608000408668544493926415504680968679321075787234672564 --gx=19277929113566293071110308034699488026831934219452440156649784352033 --gy=19926808758034470970197974370888749184205991990603949537637343198772 --order=26959946667150639794667015087019625940457807714424391721682722368061 --cofactor=1 --add-test-vectors=2

# SECP256R1
echo "SECP256R1"
$PYTHON $EXPAND_LIBECC --name="SECP256R1" --prime=115792089210356248762697446949407573530086143415290314195533631308867097853951 --a=115792089210356248762697446949407573530086143415290314195533631308867097853948 --b=41058363725152142129326129780047268409114441015993725554835256314039467401291 --gx=48439561293906451759052585252797914202762949526041747995844080717082404635286 --gy=36134250956749795798585127919587881956611106672985015071877198253568414405109 --order=115792089210356248762697446949407573529996955224135760342422259061068512044369 --cofactor=1 --add-test-vectors=2

# SECP384R1
echo "SECP384R1"
$PYTHON $EXPAND_LIBECC --name="SECP384R1" --prime=39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319 --a=39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112316 --b=27580193559959705877849011840389048093056905856361568521428707301988689241309860865136260764883745107765439761230575 --gx=26247035095799689268623156744566981891852923491109213387815615900925518854738050089022388053975719786650872476732087 --gy=8325710961489029985546751289520108179287853048861315594709205902480503199884419224438643760392947333078086511627871 --order=39402006196394479212279040100143613805079739270465446667946905279627659399113263569398956308152294913554433653942643 --cofactor=1 --add-test-vectors=2

# SECP521R1
echo "SECP521R1"
$PYTHON $EXPAND_LIBECC --name="SECP521R1" --prime=6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151 --a=6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057148 --b=1093849038073734274511112390766805569936207598951683748994586394495953116150735016013708737573759623248592132296706313309438452531591012912142327488478985984 --gx=2661740802050217063228768716723360960729859168756973147706671368418802944996427808491545080627771902352094241225065558662157113545570916814161637315895999846 --gy=3757180025770020463545507224491183603594455134769762486694567779615544477440556316691234405012945539562144444537289428522585666729196580810124344277578376784 --order=6864797660130609714981900799081393217269435300143305409394463459185543183397655394245057746333217197532963996371363321113864768612440380340372808892707005449 --cofactor=1 --add-test-vectors=2

# BRAINPOOL160R1
echo "BRAINPOOL160R1"
$PYTHON $EXPAND_LIBECC --name="BRAINPOOL160R1" --prime=1332297598440044874827085558802491743757193798159 --a=0x340E7BE2A280EB74E2BE61BADA745D97E8F7C300 --b=0x1E589A8595423412134FAA2DBDEC95C8D8675E58 --gx=0xBED5AF16EA3F6A4F62938C4631EB5AF7BDBCDBC3 --gy=0x1667CB477A1A8EC338F94741669C976316DA6321 --order=0xE95E4A5F737059DC60DF5991D45029409E60FC09 --cofactor=1 --add-test-vectors=2

# BRAINPOOL192R1
echo "BRAINPOOL192R1"
$PYTHON $EXPAND_LIBECC --name="BRAINPOOL192R1" --prime=4781668983906166242955001894344923773259119655253013193367 --a=0x6A91174076B1E0E19C39C031FE8685C1CAE040E5C69A28EF --b=0x469A28EF7C28CCA3DC721D044F4496BCCA7EF4146FBF25C9 --gx=0xC0A0647EAAB6A48753B033C56CB0F0900A2F5C4853375FD6 --gy=0x14B690866ABD5BB88B5F4828C1490002E6773FA2FA299B8F --order=0xC302F41D932A36CDA7A3462F9E9E916B5BE8F1029AC4ACC1 --cofactor=1 --add-test-vectors=2

# BRAINPOOL224R1
echo "BRAINPOOL224R1"
$PYTHON $EXPAND_LIBECC --name="BRAINPOOL224R1" --prime=22721622932454352787552537995910928073340732145944992304435472941311 --a=0x68A5E62CA9CE6C1C299803A6C1530B514E182AD8B0042A59CAD29F43 --b=0x2580F63CCFE44138870713B1A92369E33E2135D266DBB372386C400B --gx=0xD9029AD2C7E5CF4340823B2A87DC68C9E4CE3174C1E6EFDEE12C07D --gy=0x58AA56F772C0726F24C6B89E4ECDAC24354B9E99CAA3F6D3761402CD --order=0xD7C134AA264366862A18302575D0FB98D116BC4B6DDEBCA3A5A7939F --cofactor=1 --add-test-vectors=2

# BRAINPOOL256R1
echo "BRAINPOOL256R1"
$PYTHON $EXPAND_LIBECC --name="BRAINPOOL256R1" --prime=76884956397045344220809746629001649093037950200943055203735601445031516197751 --a=0x7D5A0975FC2C3057EEF67530417AFFE7FB8055C126DC5C6CE94A4B44F330B5D9 --b=0x26DC5C6CE94A4B44F330B5D9BBD77CBF958416295CF7E1CE6BCCDC18FF8C07B6 --gx=0x8BD2AEB9CB7E57CB2C4B482FFC81B7AFB9DE27E1E3BD23C23A4453BD9ACE3262 --gy=0x547EF835C3DAC4FD97F8461A14611DC9C27745132DED8E545C1D54C72F046997 --order=0xA9FB57DBA1EEA9BC3E660A909D838D718C397AA3B561A6F7901E0E82974856A7 --cofactor=1 --add-test-vectors=2

# BRAINPOOL320R1
echo "BRAINPOOL320R1"
$PYTHON $EXPAND_LIBECC --name="BRAINPOOL320R1" --prime=1763593322239166354161909842446019520889512772719515192772960415288640868802149818095501499903527 --a=0x3EE30B568FBAB0F883CCEBD46D3F3BB8A2A73513F5EB79DA66190EB085FFA9F492F375A97D860EB4 --b=0x520883949DFDBC42D3AD198640688A6FE13F41349554B49ACC31DCCD884539816F5EB4AC8FB1F1A6 --gx=0x43BD7E9AFB53D8B85289BCC48EE5BFE6F20137D10A087EB6E7871E2A10A599C710AF8D0D39E20611 --gy=0x14FDD05545EC1CC8AB4093247F77275E0743FFED117182EAA9C77877AAAC6AC7D35245D1692E8EE1 --order=0xD35E472036BC4FB7E13C785ED201E065F98FCFA5B68F12A32D482EC7EE8658E98691555B44C59311 --cofactor=1 --add-test-vectors=2

# BRAINPOOL384R1
echo "BRAINPOOL384R1"
$PYTHON $EXPAND_LIBECC --name="BRAINPOOL384R1" --prime=21659270770119316173069236842332604979796116387017648600081618503821089934025961822236561982844534088440708417973331 --a=0x7BC382C63D8C150C3C72080ACE05AFA0C2BEA28E4FB22787139165EFBA91F90F8AA5814A503AD4EB04A8C7DD22CE2826 --b=0x4A8C7DD22CE28268B39B55416F0447C2FB77DE107DCD2A62E880EA53EEB62D57CB4390295DBC9943AB78696FA504C11 --gx=0x1D1C64F068CF45FFA2A63A81B7C13F6B8847A3E77EF14FE3DB7FCAFE0CBD10E8E826E03436D646AAEF87B2E247D4AF1E --gy=0x8ABE1D7520F9C2A45CB1EB8E95CFD55262B70B29FEEC5864E19C054FF99129280E4646217791811142820341263C5315 --order=0x8CB91E82A3386D280F5D6F7E50E641DF152F7109ED5456B31F166E6CAC0425A7CF3AB6AF6B7FC3103B883202E9046565 --cofactor=1 --add-test-vectors=2

# BRAINPOOL512R1
echo "BRAINPOOL512R1"
$PYTHON $EXPAND_LIBECC --name="BRAINPOOL512R1" --prime=8948962207650232551656602815159153422162609644098354511344597187200057010413552439917934304191956942765446530386427345937963894309923928536070534607816947 --a=0x7830A3318B603B89E2327145AC234CC594CBDD8D3DF91610A83441CAEA9863BC2DED5D5AA8253AA10A2EF1C98B9AC8B57F1117A72BF2C7B9E7C1AC4D77FC94CA --b=0x3DF91610A83441CAEA9863BC2DED5D5AA8253AA10A2EF1C98B9AC8B57F1117A72BF2C7B9E7C1AC4D77FC94CADC083E67984050B75EBAE5DD2809BD638016F723 --gx=0x81AEE4BDD82ED9645A21322E9C4C6A9385ED9F70B5D916C1B43B62EEF4D0098EFF3B1F78E2D0D48D50D1687B93B97D5F7C6D5047406A5E688B352209BCB9F822 --gy=0x7DDE385D566332ECC0EABFA9CF7822FDF209F70024A57B1AA000C55B881F8111B2DCDE494A5F485E5BCA4BD88A2763AED1CA2B2FA8F0540678CD1E0F3AD80892 --order=0xAADD9DB8DBE9C48B3FD4E6AE33C9FC07CB308DB3B3C9D20ED6639CCA70330870553E5C414CA92619418661197FAC10471DB1D381085DDADDB58796829CA90069 --cofactor=1 --add-test-vectors=2
