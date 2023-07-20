function modSNARK(hexNum) {
    p = 21888242871839275222246405745257275088548364400416034343698204186575808495617n;
    res = '0x' + (BigInt(parseInt(hexNum, 16)) % p).toString(16).padStart(64, '0');
    return res;
}

function nxtPo2(x) {
    x--;
    x = x | (x >> 1);
    x = x | (x >> 2);
    x = x | (x >> 4);
    x = x | (x >> 8);
    x = x | (x >> 16);
    x = x | (x >> 32);
    x++;
    return x;
}

module.exports = {
    nxtPo2,
    modSNARK
};
