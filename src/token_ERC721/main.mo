import Nat "mo:base/Nat";
import Hash "mo:base/Hash";
import Text "mo:base/Text";
import List "mo:base/List";
import Time "mo:base/Time";
import Iter "mo:base/Iter";
import Array "mo:base/Array";
import Error "mo:base/Error";
import Option "mo:base/Option";
import Result "mo:base/Result";
import TrieSet "mo:base/TrieSet";
import Prelude "mo:base/Prelude";
import HashMap "mo:base/HashMap";
import Principal "mo:base/Principal";

/**
 *  Implementation of https://github.com/icplabs/DIPs/blob/main/DIPS/dip-721.md Non-Fungible Token Standard.
 */
shared(msg) actor class Token_ERC721(_name: Text, _symbol: Text, admin: Principal) = this {
    type TokenActor = actor {
        transferFrom : (from: Principal, to: Principal, value: Nat) -> async TxReceipt;
    };

    type TxReceipt = Result.Result<Nat, {
        #InsufficientBalance;
        #InsufficientAllowance;
    }>;

    type TokenInfo = {
        createTime: Time.Time;
        var owner: Principal;
        var url: Text;
        var tokenName: Text;
        var tokenDescription: Text;
        var approver: ?Principal;
    };

    type UserInfo = {
        var operatedBy: TrieSet.Set<Principal>;     // owner 允许这些人代替他操作，用于权限检查。
        var operate: TrieSet.Set<Principal>;        // owner 可以操作的账号，仅用于快速查询
        var operateId: TrieSet.Set<Nat>;            // owner 可以操作的 id，仅用于快速查询
        var tokens: TrieSet.Set<Nat>;               // owner 拥有的 id
        var favourites: TrieSet.Set<Nat>;           // owner 喜欢的 id
    };

    type TokenInfoExt = {
        createTime: Time.Time;
        owner: Principal;
        url: Text;
        tokenName: Text;
        tokenDescription: Text;
        approver: ?Principal;
    };

    type UserInfoExt = {
        operatedBy: [Principal];
        operate: [Principal];
        operateId: [Nat];
        tokens: [Nat];
        favourites: [Nat];
    };

    private stable var name_ : Text = _name;
    private stable var symbol_ : Text = _symbol;
    private stable var tokenIdMark_ : Nat = 1;
    private stable var erc20TokenCanister : Principal = admin;
    private stable var mintPrice : Nat = 0;
    private stable var mintFeePool : Principal = admin; 
    private var admins = HashMap.HashMap<Principal, Bool>(1, Principal.equal, Principal.hash);
    private var tokenInfos_ = HashMap.HashMap<Nat, TokenInfo>(1, Nat.equal, Hash.hash);
    private var userInfos_ = HashMap.HashMap<Principal, UserInfo>(1, Principal.equal, Principal.hash);
   
    admins.put(admin, true);

    // private query function

    private func _unwrap<T>(x : ?T) : T =
    switch x {
      case null { Prelude.unreachable() };
      case (?x_) { x_ };
    };
    /**
     * @dev Returns whether the specified token exists
     * @param tokenId uint256 ID of the token to query the existence of
     * @return whether the token exists
     */
    private func _exists(tokenId: Nat) : Bool {
        switch (tokenInfos_.get(tokenId)) {
            case (?token) { return true; };
            case _ { return false; };
        }
    };

    private func _ownerOf(tokenId: Nat) : ?Principal {
        switch (tokenInfos_.get(tokenId)) {
            case (?token) { return ?token.owner; };
            case _ { return null };
        };
    };

    private func _isOwner(who: Principal, tokenId: Nat) : Bool {
        switch (tokenInfos_.get(tokenId)) {
            case (?token) { return token.owner == who; };
            case _ { return false; };
        };
    };

    private func _isApprover(who: Principal, tokenId: Nat) : Bool {
        switch (tokenInfos_.get(tokenId)) {
            case (?token) { return token.approver == ?who; };
            case _ { return false; };
        };        
    };

    private func _isOperator(owner: Principal, operator: Principal) : Bool {
        switch (userInfos_.get(owner)) {
            case (?user) {
                return TrieSet.mem(user.operatedBy, operator, Principal.hash(operator), Principal.equal);
            };
            case _ { return false; };
        };
    };

    private func _balanceOf(who: Principal) : Nat {
        switch (userInfos_.get(who)) {
            case (?user) { return TrieSet.size(user.tokens); };
            case _ { return 0; };
        };
    };

    private func _newUser() : UserInfo {
        {
            var operatedBy = TrieSet.empty<Principal>();
            var operate = TrieSet.empty<Principal>();
            var operateId = TrieSet.empty<Nat>();
            var tokens = TrieSet.empty<Nat>();
            var favourites = TrieSet.empty<Nat>();
        }
    };

    private func _tokenInfotoExt(info: TokenInfo) : TokenInfoExt {
        return {
            createTime = info.createTime;
            owner = info.owner;
            url = info.url;
            tokenName = info.tokenName;
            tokenDescription = info.tokenDescription;
            approver = info.approver;
        };
    };

    private func _userInfotoExt(info: UserInfo) : UserInfoExt {
        return {
            operatedBy = TrieSet.toArray(info.operatedBy);
            operate = TrieSet.toArray(info.operate);
            operateId = TrieSet.toArray(info.operateId);
            tokens = TrieSet.toArray(info.tokens);
            favourites = TrieSet.toArray(info.favourites);
        };
    };

    /**
     * Returns whether `spender` is allowed to manage `tokenId`.
     * Requirements:
     * - `tokenId` must exist.
     */
    private func _isApprovedOrOwner(spender: Principal, tokenId: Nat) : Bool {
        switch (_ownerOf(tokenId)) {
            case (?owner) {
                return spender == owner or _isApprover(spender, tokenId) or _isOperator(owner, spender);
            };
            case _ {
                return false;
            };
        };
    };    

    // private modify function

    /**
     * @dev Internal function to add a token ID to the list of a given address
     * @param to address representing the new owner of the given token ID
     * @param tokenId uint256 ID of the token to be added to the tokens list of the given address
     */
    private func _addTokenTo(to: Principal, tokenId: Nat) {
        switch(userInfos_.get(to)) {
            case (?userInfo) {
                userInfo.tokens := TrieSet.put(userInfo.tokens, tokenId, Hash.hash(tokenId), Nat.equal);
                userInfos_.put(to, userInfo);
            };
            case _ {
                let userInfo = _newUser();
                userInfo.tokens := TrieSet.put(userInfo.tokens, tokenId, Hash.hash(tokenId), Nat.equal);
                userInfos_.put(to, userInfo);
            };
        }
    };

    /**
     * @dev Internal function to remove a token ID from the list of a given address
     * @param from address representing the previous owner of the given token ID
     * @param tokenId uint256 ID of the token to be removed from the tokens list of the given address
     */
    private func _removeTokenFrom(owner: Principal, tokenId: Nat) {
        assert(_exists(tokenId) and _isOwner(owner, tokenId));
        switch(userInfos_.get(owner)) {
            case (?userInfo) {
                userInfo.tokens := TrieSet.delete(userInfo.tokens, tokenId, Hash.hash(tokenId), Nat.equal);
                userInfos_.put(owner, userInfo);
            };
            case _ {
                assert(false);
            };
        }
    };

    private func _clearApproval(owner: Principal, tokenId: Nat) {
        assert(_exists(tokenId) and _isOwner(owner, tokenId));
        switch (tokenInfos_.get(tokenId)) {
            case (?tokenInfo) {
                tokenInfo.approver := null;
                tokenInfos_.put(tokenId, tokenInfo);
            };
            case _ {
                assert(false);
            };
        }
    };

    /**
    * @dev private function to mint a new token
    * Reverts if the given token ID already exists
    * @param to The address that will own the minted token
    * @param tokenId Nat ID of the token to be minted by the msg.sender
    */
    private func _mint(to: Principal, tokenId: Nat, url: Text, tokenName: Text, tokenDescription: Text) {
        assert(_exists(tokenId) == false);
        let token: TokenInfo = {
            createTime = Time.now();
            var owner = to;
            var url = url;
            var tokenName = tokenName;
            var tokenDescription = tokenDescription;
            var approver = null;
        };
        tokenInfos_.put(tokenId, token);        
        _addTokenTo(to, tokenId);
    };    

    /**
    * @dev Internal function to burn a specific token
    * Reverts if the token does not exist
    * @param tokenId uint256 ID of the token being burned by the msg.sender
    */
    private func _burn(owner: Principal, tokenId: Nat) {

        _removeTokenFrom(owner, tokenId);
        tokenInfos_.delete(tokenId);

    };

    // set Token Info
    private func _setTokenInfo(tokenId : Nat, uri: Text, name: Text, description: Text) {
        assert(_exists(tokenId));
        switch (tokenInfos_.get(tokenId)) {
            case (?info) {
                info.url := uri;
                info.tokenName := name;
                info.tokenDescription := description;
                tokenInfos_.put(tokenId, info);
            };
            case _ {
                assert(false);
            };
        }  
    };

    private func _changeTokenInfoOwner(tokenId: Nat, owner: Principal) {
        assert(_exists(tokenId));
        switch (tokenInfos_.get(tokenId)) {
            case (?info) {
                info.owner := owner;
                tokenInfos_.put(tokenId, info);
            };
            case _ {
                assert(false);
            };
        }
    };

    /**
     * @dev Transfers `tokenId` from `from` to `to`.
     *  As opposed to {transferFrom}, this imposes no restrictions on msg.caller.
     *
     * Requirements:
     * - `tokenId` token must be owned by `from`.
     */
    private func _transferFrom(caller: Principal, from: Principal, to: Principal, tokenId: Nat) {
        assert(_isApprovedOrOwner(caller, tokenId));
        _clearApproval(from, tokenId);
        _removeTokenFrom(from, tokenId);
        _addTokenTo(to, tokenId);
        _changeTokenInfoOwner(tokenId, to);
    };    

    // public query function 

    /**
     * Token name
     */
    public query func name() : async Text {
        return name_;
    };

    /**
     * Token symbol
     */
    public query func symbol() : async Text {
        return symbol_;
    };

    /**
     * @dev See {IERC721Metadata-tokenURI}.
     */
    public query func tokenInfo(tokenId: Nat) : async TokenInfoExt {
        switch(tokenInfos_.get(tokenId)){
            case(?tokeninfo){
                return _tokenInfotoExt(tokeninfo);
            };
            case _ {
                throw Error.reject("ERC721Metadata: info query for nonexistent token");
            };
        };
    };

    /*
     * @notice Find the owner of an NFT
     * NFTs assigned to the zero address are considered invalid, 
     * and queries about them do throw.
     * @param _tokenId The identifier for an NFT
     * @return The address of the owner of the NFT
     */
     public query func ownerOf(tokenId: Nat) : async Principal {
        switch (_ownerOf(tokenId)) {
            case (?owner) {
                return owner;
            };
            case _ {
                throw Error.reject("token does not exist, can't get owner")
            };
        }
    };


    /*
     * @notice Count all NFTs assigned to an owner
     * NFTs assigned to the zero address are considered invalid, 
     * and this function throws for queries about the zero address.
     * @param _owner An address for whom to query the balance
     * @return The number of NFTs owned by `_owner`, possibly zero
     */
    public query func balanceOf(who: Principal) : async Nat {
        _balanceOf(who)
    };

    /**
     * @dev Gets the approved address for a token ID, or zero if no address set
     * Reverts if the token ID does not exist.
     * @param tokenId uint256 ID of the token to query the approval of
     * @return address currently approved for the given token ID
     */    
    public query func getApproved(tokenId: Nat) : async ?Principal {
        switch (tokenInfos_.get(tokenId)) {
            case (?token) { return token.approver; };
            case _ { return null };
        }
    };

    /*
     * @notice Query if an address is an authorized operator for another address
     * @param _owner The address that owns the NFTs
     * @param _operator The address that acts on behalf of the owner
     * @return True if `_operator` is an approved operator for `_owner`, false otherwise
     */
    public query func isApprovedForAll(owner: Principal, operator: Principal) : async Bool {
        return _isOperator(owner, operator);
    };

    public query func tokenOfOwnerByIndex(owner: Principal, index: Nat) : async Nat {
        let balance = _balanceOf(owner);
        assert(index < balance);
        switch (userInfos_.get(owner)) {
            case (?userInfo) {
                return TrieSet.toArray(userInfo.tokens)[index];
            };
            case _ {
                throw Error.reject("owner don't have the token index")
            };
        };
    };

    public query func totalSupply() : async Nat {
        return tokenInfos_.size()
    };

    public query func tokenByIndex(index: Nat) : async Nat {
        assert(index < tokenInfos_.size());
        let tokenIds = Iter.toArray(Iter.map(tokenInfos_.entries(), func (i: (Nat, TokenInfo)): Nat {i.0}));
        return tokenIds[index];
    };

    public query func getAllTokens() : async [Nat] {
        let tokenIds = Iter.toArray(Iter.map(tokenInfos_.entries(), func (i: (Nat, TokenInfo)): Nat {i.0}));
        return tokenIds;
    };

    public query func getTokenList(owner: Principal) : async [Nat] {
        switch (userInfos_.get(owner)) {
            case (?userInfo) {
                return TrieSet.toArray(userInfo.tokens);
            };
            case _ {
                throw Error.reject("can't get the principal's ownedTokens");
            };
        };
    };

    public query func isAdmin(who: Principal) : async Bool {
        switch (admins.get(who)) {
            case (?res) {
                return res;                
            };
            case _ {
                return false;
            };
        }
    };

    public query func tokenCanisterId() : async Principal {
        return erc20TokenCanister;
    };

    public query func mintNftPrice() : async Nat {
        return mintPrice;
    };

    public query func mintFeePoolId() : async Principal {
        return mintFeePool;
    };

    // public modify function 

    /*
     * @notice Change or reaffirm the approved address for an NFT
     * The zero address indicates there is no approved address.
     * Throws unless `msg.caller` is the current NFT owner, or an authorized operator of the current owner.
     * @param spender The new approved NFT controller
     * @param tokenId The NFT to approve
     */
    public shared(msg) func approve(spender: Principal, tokenId: Nat) : async Bool {
        assert(_isOwner(msg.caller, tokenId));
        assert(msg.caller != spender);
        switch (tokenInfos_.get(tokenId)) {
            case (?tokenInfo) {
                tokenInfo.approver := ?spender;
                tokenInfos_.put(tokenId, tokenInfo);
            };
            case _ {
                assert(false);
            };
        };
        switch (userInfos_.get(spender)) {
            case (?userInfo) {
                userInfo.operateId := TrieSet.put(userInfo.operateId, tokenId, Hash.hash(tokenId), Nat.equal);
                userInfos_.put(spender, userInfo);
            };
            case _ {
                assert(false);
            };
        };
        return true;
    };

    /*
     * @notice Enable or disable approval for a third party ("operator") to manage all of `msg.caller`'s assets
     * The contract MUST allow multiple operators per owner.
     * Throws unless `msg.caller` is the current NFT owner, or an authorized operator of the current owner.
     * @param _operator Address to add to the set of authorized operators
     * @param _approved True if the operator is approved, false to revoke approval
     */
    public shared(msg) func setApprovalForAll(operator: Principal, approved: Bool) : async Bool {
        assert(msg.caller != operator);
        if approved {
            switch (userInfos_.get(msg.caller)) {
                case (?userInfo) {
                    userInfo.operatedBy := TrieSet.put(userInfo.operatedBy, operator, Principal.hash(operator), Principal.equal);    
                    userInfos_.put(msg.caller, userInfo);
                };
                case _ {
                    let userInfo = _newUser();
                    userInfo.operatedBy := TrieSet.put(userInfo.operatedBy, operator, Principal.hash(operator), Principal.equal);
                    userInfos_.put(msg.caller, userInfo);
                };
            };
            switch (userInfos_.get(operator)) {
                case (?userInfo) {
                    userInfo.operate := TrieSet.put(userInfo.operate, msg.caller, Principal.hash(msg.caller), Principal.equal);    
                    userInfos_.put(operator, userInfo);
                };
                case _ {
                    let userInfo = _newUser();
                    userInfo.operate := TrieSet.put(userInfo.operate, msg.caller, Principal.hash(msg.caller), Principal.equal);
                    userInfos_.put(operator, userInfo);
                };
            };
        } else {
            switch (userInfos_.get(msg.caller)) {
                case (?userInfo) {
                    userInfo.operatedBy := TrieSet.delete(userInfo.operatedBy, operator, Principal.hash(operator), Principal.equal);    
                    userInfos_.put(msg.caller, userInfo);
                };
                case _ { };
            };
            switch (userInfos_.get(operator)) {
                case (?userInfo) {
                    userInfo.operate := TrieSet.delete(userInfo.operate, msg.caller, Principal.hash(msg.caller), Principal.equal);    
                    userInfos_.put(operator, userInfo);
                };
                case _ { };
            };
        };
        return true;
    };

    /*
     * @notice Transfer ownership of an NFT
     * THE CALLER IS RESPONSIBLE TO CONFIRM THAT `_to` IS CAPABLE OF RECEIVING NFTS 
     * OR ELSE THEY MAY BE PERMANENTLY LOST
     * Throws unless `msg.sender` is the current owner, an authorized operator, or the approved address for this NFT. 
     * Throws if `_from` is not the current owner. Throws if `_to` is the zero address. Throws if `_tokenId` is not a valid NFT.
     * @param _from The current owner of the NFT.
     * @param _to The new owner.
     * @param _tokenId The NFT to transfer
     */
    public shared(msg) func transferFrom(from: Principal, to: Principal, tokenId: Nat) : async Bool {
        _transferFrom(msg.caller, from, to, tokenId);
        return true;
    };

    public shared(msg) func setTokenInfo(tokenId: Nat, uri: Text, tokenName: Text, tokenDescription: Text) : async Bool {
        assert(_unwrap(_ownerOf(tokenId)) == msg.caller);
        _setTokenInfo(tokenId, uri, tokenName, tokenDescription);
        return true;
    };

    public shared(msg) func mint(to: Principal, tokenUrl: Text, tokenName: Text, tokenDescription: Text) : async Nat {
        let erc20 : TokenActor = actor(Principal.toText(erc20TokenCanister));
        Result.assertOk(await erc20.transferFrom(msg.caller, mintFeePool, mintPrice));
        let tokenId = tokenIdMark_;
        tokenIdMark_ +=  1;
        _mint(to, tokenId, tokenUrl, tokenName, tokenDescription);
        return tokenId;
    };

    public shared(msg) func burn(tokenId: Nat) : async Bool {
        assert(_unwrap(admins.get(msg.caller)));
        assert(_exists(tokenId));
        let to = switch (_ownerOf(tokenId)) {
            case (?owner) {
                owner;
            };
            case _ {
                throw Error.reject("can't get the token owner");
            }
        };
        _burn(to, tokenId);
        return true;
    };

    public shared(msg) func withdraw(tokenId: Nat, to: Principal) : async Bool {
        assert(_exists(tokenId));
        assert(_unwrap(admins.get(msg.caller)));
        let owner = Principal.fromActor(this);
        assert(_unwrap(_ownerOf(tokenId)) == owner);
        _clearApproval(owner, tokenId);
        _removeTokenFrom(owner, tokenId);
        _addTokenTo(to, tokenId);
        return true;
    };

    public shared(msg) func setAdmin(who: Principal, isOr: Bool) : async Bool {
        assert(_unwrap(admins.get(msg.caller)));
        admins.put(who, isOr);
        return true;
    };

    public shared(msg) func setErc20(token: Principal) : async Bool {
        assert(_unwrap(admins.get(msg.caller)));
        erc20TokenCanister := token;
        return true;
    };

    public shared(msg) func setFeePrice(price: Nat) : async Bool {
        assert(_unwrap(admins.get(msg.caller)));
        mintPrice := price;
        return true;
    };

    public shared(msg) func setFeePool(pool: Principal) : async Bool {
        assert(_unwrap(admins.get(msg.caller)));
        mintFeePool := pool;
        return true;
    };

    public shared(msg) func favourite(tokenId: Nat) : async Bool {
        assert(_exists(tokenId));
        switch (userInfos_.get(msg.caller)) {
            case (?userInfo) {
                userInfo.favourites := TrieSet.put(userInfo.favourites, tokenId, Hash.hash(tokenId), Nat.equal);
                userInfos_.put(msg.caller, userInfo);
            };
            case _ {
                let userInfo = _newUser();
                userInfo.favourites := TrieSet.put(userInfo.favourites, tokenId, Hash.hash(tokenId), Nat.equal);
                userInfos_.put(msg.caller, userInfo);
            };
        };
        return true;
    };

    public query func getFavourites(who: Principal) : async [Nat] {
        switch (userInfos_.get(who)) {
            case (?userInfo) {
                return TrieSet.toArray(userInfo.favourites);
            };
            case _ {
                return [];
            };
        }
    };

    public query func getFavouritedBy(tokenId: Nat) : async [Principal] {
        var temp : [Principal] = [];
        for ((k, v) in userInfos_.entries()) {
            if (TrieSet.mem(v.tokens, tokenId, Hash.hash(tokenId), Nat.equal)) {
                temp := Array.append(temp, [k]);
            };
        };
        return temp;
    };
};
