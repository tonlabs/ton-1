#!/bin/bash -eE

SCRIPT_DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)

URL="https://github.com/tonlabs/ton-labs-contracts/raw/master/solidity/safemultisig"
rm -f SafeMultisigWallet.tvc
rm -f SafeMultisigWallet.abi.json
wget "$URL/SafeMultisigWallet.tvc"
wget "$URL/SafeMultisigWallet.abi.json"
rm -f SetcodeMultisigWallet.tvc
rm -f SetcodeMultisigWallet.abi.json
URL="https://github.com/tonlabs/ton-labs-contracts/raw/master/solidity/setcodemultisig"
wget "$URL/SetcodeMultisigWallet.tvc"
wget "$URL/SetcodeMultisigWallet.abi.json"

ZERO="0000000000000000000000000000000000000000000000000000000000000000"

if [ -z "${INIT_WALLETS_FILE}" ]; then
    echo "ERROR: INIT_WALLETS_FILE not defined"
    exit 1
fi

while IFS= read -r line; do
    if [ "$(echo "$line" | grep ^entry)" != "" ]; then
        PUBKEY=$(echo "$line" | cut -d ' ' -f 4)
        NAME=$(echo "$line" | cut -d ' ' -f 2)
        NAME="${NAME%\"}"
        NAME="${NAME#\"}"
        echo "{ \"public\": ${PUBKEY}, \"secret\": \"${ZERO}\" }" >deploy.keys.json
        cp SafeMultisigWallet.tvc "/home/ruser/shared/private/common/${NAME}SafeMultisigWallet.tvc"
        /utils/tonos-cli genaddr "/home/ruser/shared/private/common/${NAME}SafeMultisigWallet.tvc" SafeMultisigWallet.abi.json --setkey deploy.keys.json --wc -1 --save
    fi

    if [ "$(echo "$line" | grep ^giver)" != "" ]; then
        PUBKEY=$(echo "$line" | cut -d ' ' -f 5)
        NAME=$(echo "$line" | cut -d ' ' -f 2)
        NAME="${NAME%\"}"
        NAME="${NAME#\"}"
        echo "{ \"public\": ${PUBKEY}, \"secret\": \"${ZERO}\" }" >deploy.keys.json
        cp SetcodeMultisigWallet.tvc "/home/ruser/shared/private/common/${NAME}SetcodeMultisigWallet.tvc"
        /utils/tonos-cli genaddr "/home/ruser/shared/private/common/${NAME}SetcodeMultisigWallet.tvc" SetcodeMultisigWallet.abi.json --setkey deploy.keys.json --wc -1 --save
    fi
done <"${SCRIPT_DIR}/${INIT_WALLETS_FILE}"

rm -f SafeMultisigWallet.tvc
rm -f SafeMultisigWallet.abi.json
rm -f SetcodeMultisigWallet.tvc
rm -f SetcodeMultisigWallet.abi.json
rm -f deploy.keys.json
